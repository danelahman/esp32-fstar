(**
  * An example F*/Low* application that switches a LED on and off on 
  * an ESP32 board by installing an interrupt handler that then reacts
  * to pushes of a button.
  *
  *)
  
(**
  * (Some) **safety requirements** on the (memory) safety of this ESP32
  * application, but which apply more generally to embedded IoT code:
  * 
  * 1. While the GPIO library function `gpio_isr_handler_add` requires
  *    the resources (i.e., `led_status`) to be passed to the interrupt
  *    handler as a void pointer, we want to be sure that it is safe 
  *    to downcast a the void pointer passed to `set_led_status` into
  *    an unsigned integer of given size (e.g., of 8 bits).
  *
  * 2. The `led_status` pointer, which instructs what state (on or off
  *    to set the LED to, should **follow an invariant** that its value 
  *    remains between 0 and 1.
  *
  *    More generally, we would like such invariants to hold to ensure
  *    that, e.g., motors and servos never move beyond allowed parameters.
  *
  * 3. Once a resource such as `led_status` is assigned to an interrupt
  *    handler, it **should not be freed** by other parts of the code
  *    before the given interrupt handler is uninstalled. 
  *
  *    Otherwise, if a different part of the program frees the resource, 
  *    then when the interrupt handler is invoked we will get a segfault.
  *
  *    More generally, we could also want to ensure that only a select
  *    few parts of the program can access and modify a resource while
  *    it is being held by some installed interrupt handler.
  *
  * 4. We should only be able to install an interrupt handler and set 
  *    its type **after we have set up** the interrupt handler service.
  *
  * 5. The interrupt handler code **should only modify** the resources 
  *    we give it explicitly, and not modify other parts of the memory, 
  *    such as the resources of other interrupt handlers, or the internals
  *    of the ESP and GPIO libraries.
  *
  *)

(**
  * We ensure that these **safety requirements are satisfied** as follows:
  * 
  * 1. We define our custom void pointer library in F* in such a way that
  *    we keep track of what type's upcast a given void pointer is, and
  *    only downcast a void pointer to its corresponding original type.
  * 
  * 2. We define `led_status` as a monotonic buffer with a preorder (see 
  *    `led_status_rel`) that constrains the evolution of `led_status`
  *    so that once its length is 1 (i.e., it's a pointer) and its value
  *    has been set to 0 or 1, it will forever on keep this length and
  *    value range.
  *
  *    Bonus: Using monotonicity, we can always recall (using `recall_p`)
  *           any stable property of `led_status` we have previously
  *           witnessed, such as that its length is 1. and its value is 
  *           between 0 and 1. As a result, we do not need to thread such
  *           invariants through the pre- and postconditions of the rest
  *           of our program.
  *
  * 3. First, we consider a piece of ghost state (see `ESPST.isr_map`) 
  *    that stores a map from I/O pins to the resources that installed
  *    interrupt handlers associated with these pins hold.
  *
  *    Second, we implement our program in a specially defined effect 
  *    `ESPST`, which refines Low*'s standard standard state effect by
  *    requiring that any resources marked as being in use by the ghost
  *    state have to be allocated and live in the actual memory.
  *
  *    Third, for a more predictable programming model, we require (in 
  *    the spec. of `gpio_isr_handler_add`) that any interrupt handler
  *    code has to be written so that it modifies at most the resources
  *    we explicitly pass to it. As a result, it cannot modify the ghost
  *    state, i.e., uninstall existing or install new interrupt handlers.
  *
  *    More generally, this kind of ghost state approach could also
  *    be used to mark which parts of the memory which parts of the
  *    program have access to.
  *
  * 4. We have assigned the interrupt handler related GPIO library
  *    functions specifications that require the ghost state modelling
  *    the resources held by installed interrupt handlers to be in a 
  *    specific shape. 
  *
  *    For example, we require that when calling the `gpio_isr_handler_add` 
  *    function, then the given I/O pin must not have an active interrupt 
  *    handler set, and ensure that after`gpio_isr_handler_add` the resource 
  *    given to it has been marked as being in use by the ghost state.
  *
  * 5. To ensure that interrupt handler code only changes its own 
  *    footprint, i.e., the resources we explicitly give it, we use 
  *    Low*'s `modifies` clauses that specify which (pre-existing)
  *    memory locations a given program might have modified.
  * 
  *)

module Main

module B = LowStar.Buffer
module U32 = FStar.UInt32

module HS = FStar.HyperStack
module MHS = FStar.Monotonic.HyperStack

open GPIO.Constants
open GPIO
open ESPST

module VP = Monotonic.VoidPointer
module VPU32 = Monotonic.VoidPointer.UInt32
module VPW = Monotonic.VoidPointer.While


(**
  * The GPIO pins of the button and the LED:
  *)
let button_gpio = gpio_num_0
let led_gpio = gpio_num_5


(**
  * A preorder that governs how the pointer we use to track the
  * status of the LED is allowed to evolve: once initialised
  * with value 0ul or 1ul, it can never go beyond these values.
  * This ensures that no other part of the program can invalidate
  * the invariant of the ISR handler for turning the LED on and off, 
  * which his that the pointer needs to remain valued 0ul or 1ul.
  *)
noextract
let led_status_rel : B.srel U32.t =
  fun i0 i1 ->
    (FStar.Seq.length i0 = 1 /\ (FStar.Seq.index i0 0 = 0ul \/ FStar.Seq.index i0 0 = 1ul) 
     ==> 
     FStar.Seq.length i1 = 1 /\ (FStar.Seq.index i1 0 = 0ul \/ FStar.Seq.index i1 0 = 1ul))

(**
  * Predicate describing that (the LED status) pointer
  * has been initialised with a value 0ul or 1ul. Properties
  * of monotonic state then ensure that in any subsequent 
  * state evolution the pointer remains valued at 0ul or 1ul.
  *)
noextract
let led_status_initialised_pred : B.spred U32.t =
  fun i ->  FStar.Seq.length i = 1 /\
         (FStar.Seq.index i 0 = 0ul \/ FStar.Seq.index i 0 = 1ul)

noextract
let led_status_initialised (p:B.mpointer U32.t led_status_rel led_status_rel) : Type0 =
  B.witnessed p led_status_initialised_pred


(**
  * The precondition of `set_led_status`, it requires that:
  * - the given void pointer is an upcast of an `uint32_t` pointer 
  *   with `led_status_rel` preorder,
  * - the given void pointer is live,
  * - the given void pointer is disjoint from the ghost state, and
  * - the given void pointer has once been initialised with 0 or 1.
  *)
noextract
let set_led_status_pre (led_status: VP.t) (h0: HS.mem) : GTot Type0 =
  led_status `VP.is_upcast_of` led_status_rel /\ 
  B.live h0 (VP.g_downcast led_status_rel led_status) /\
  isr_disjoint_from (VP.g_downcast led_status_rel led_status) /\
  led_status_initialised (VP.g_downcast led_status_rel led_status)

(**
  * The postcondition `set_led_status`, it ensures that:
  * - the `uint32_t` value of the given void pointer remains 0ul or 1ul, and
  * - the function only modifies the given void pointer.
  *)
noextract
let set_led_status_post (led_status: VP.t) (h0: HS.mem) (_: unit) (h1: HS.mem)
    : GTot Type0 =
  led_status `VP.is_upcast_of` led_status_rel /\
  B.modifies (B.loc_buffer (VP.g_downcast led_status_rel led_status)) h0 h1

(**
  * Two auxiliary lemmas proving that after changing the void pointer 
  * in `set_led_status`, it remains assigned the value 0ul or 1ul. 
  *)
noextract
let set_led_status_lemma0 (x: U32.t)
    : Lemma (requires (x = 0ul))
      (ensures (U32.logand (x `U32.add` 1ul) 1ul = 1ul))
      [SMTPat (U32.logand (x `U32.add` 1ul) 1ul)] =
  assert (x `U32.add` 1ul = 1ul);
  assert (U32.logand 1ul 1ul = 1ul)

noextract
let set_led_status_lemma1 (x: U32.t)
    : Lemma (requires (x = 1ul))
      (ensures (U32.logand (x `U32.add` 1ul) 1ul = 0ul))
      [SMTPat (U32.logand (x `U32.add` 1ul) 1ul)] =
  assert (x `U32.add` 1ul = 2ul);
  assert (U32.logand 2ul 1ul = 0ul)

(**
  * Interrupt handler code that flips the value of `led_status`
  * from 0ul to 1ul, and vice versa, resulting in the
  * associated LED being turned either on or off.
  *)
noextract
inline_for_extraction
let set_led_status_espst (led_status: VP.t)
    : ESPST unit
      (requires (set_led_status_pre led_status))
      (ensures (set_led_status_post led_status)) =
  recall isr_map;
  let led = VPU32.downcast led_status_rel led_status in
  recall_p led led_status_initialised_pred;
  led *= U32.logand (!*led `U32.add` 1ul) 1ul

let set_led_status (led_status: VP.t)
    : ESPST_Extract unit
      (requires (set_led_status_pre led_status))
      (ensures (set_led_status_post led_status)) =
  extract_st (fun _ -> set_led_status_espst led_status)


(**
  * The precondition of `main_task`, it requires that:
  * - the GPIO-internals are live,
  * - `led_status` is an upcast of an `uint32_t` pointer,
  * - `led_status` is live, and
  * - `led_status` is disjoint from the ghost state.
  *)
noextract
let main_task_pre (led_status: VP.t) (h0: HS.mem) : GTot Type0 =
  B.live h0 gpio_intl_bufs /\
  led_status `VP.is_upcast_of` led_status_rel /\ 
  B.live h0 (VP.g_downcast led_status_rel led_status) /\
  isr_disjoint_from (VP.g_downcast led_status_rel led_status)

(**
  * The postcondition of `main_task`, it ensures that:
  * - the function only modifies only the GPIO-internals, and
  * - the function does not modify the ghost state.
  *)
noextract
let main_task_post (led_status: VP.t) (h0: HS.mem) (_: unit) (h1: HS.mem) 
    : GTot Type0 =
  modifies_gpio_intl_bufs h0 h1 /\ isr_unmodified h0 h1

(**
  * A function that gets run in an infinite loop, 
  * and which sets the LED status (turning it on or off)
  * depending on the value of the given void pointer.
  *)
noextract
inline_for_extraction
let main_task_espst (led_status: VP.t)
    : ESPST unit (requires (main_task_pre led_status)) 
                 (ensures (main_task_post led_status)) =
  let _ = gpio_set_level led_gpio !*(VPU32.downcast led_status_rel led_status) in
  ESP.vTaskDelay (100ul `U32.div` ESP.portTICK_PERIOD_MS)

let main_task (led_status: VP.t) 
    : ESPST_Extract unit (requires (main_task_pre led_status)) 
                         (ensures (main_task_post led_status)) =
  extract_st (fun _ -> main_task_espst led_status)


(** 
  * The precondition of `app_main`, it requires that:
  * - the GPIO-internals are live, and
  * - that the ISR handler service has not been installed yet.
  *)
noextract
let app_main_pre (h0: HS.mem) : GTot Type0 = 
  B.live h0 gpio_intl_bufs /\ 
  ~(isr_installed h0)

(** 
  * The postcondition of `app_main`, it ensures that:
  * - the function only modifies GPIO-internals and the ghost
  *   state modelling arguments/resources to ISR handlers, and
  * - that the ISR handler service has been uninstalled.
  *)
noextract
let app_main_post (h0: HS.mem) (_: unit) (h1: HS.mem) : GTot Type0 = 
  modifies_gpio_intls h0 h1 /\
  ~(isr_installed h1)

(**
  * The main function and entrypoint for ESP32, it:
  * - allocates a void pointer to track GPIO button pushes, 
  * - sets up a GPIO button configuration,
  * - installs an ISR handler, and
  * - in an infinite loop it polls for any button pushes so
  *   as to change the light status of the LED.
  *)
noextract
inline_for_extraction
let app_main_espst (_: unit) 
    : ESPST unit (requires app_main_pre) (ensures app_main_post) =
  recall isr_map;
  
  // led status setup
  let led_status = mmalloc #U32.t #led_status_rel HS.root 0ul in
  witness_p led_status led_status_initialised_pred;
  let _ = gpio_pad_select_gpio led_gpio in
  let _ = gpio_set_direction led_gpio gpio_mode_output in

  // button setup
  let _ = gpio_pad_select_gpio button_gpio in
  let _ = gpio_set_direction button_gpio gpio_mode_input in
  
  // isr install
  let _ = gpio_install_isr_service esp_intr_flag_lowmed in
  let _ =
    gpio_isr_handler_add 
      #set_led_status_pre
      #set_led_status_post
      button_gpio
      set_led_status
      (VPU32.upcast led_status_rel led_status)
  in
  let _ = gpio_set_intr_type button_gpio gpio_intr_posedge in

  // while loop
  VPW.while_true #main_task_pre #main_task_post main_task (VPU32.upcast led_status_rel led_status)
  
  // isr uninstall
  // If we were to remove the infinite while loop, or have a terminating
  // loop in the code instead, we would also need to uninstall the 
  // installed ISR handlers so as to release resources (with `pop_frame`
  // in this case). This can be done by running the function given below:
  //
  // gpio_uninstall_isr_service ();



(**
  * Top-level main function that will get extracted to C.
  *)
let app_main (_: unit) 
    : ESPST_Extract unit (requires app_main_pre) (ensures app_main_post) =
  extract_st app_main_espst
