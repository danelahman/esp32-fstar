(**
  * An example F*/Low* application that switches between two LED
  * blinking modes (slower and faster) on an ESP32 board by 
  * installing an interrupt handler that reacts and changes the
  * blinking mode when a button is pushed.
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
  * currently active blinking mode is allowed to evolve: once
  * initialised with 0ul or 1ul, it can never go beyond these values.
  *)
noextract
let led_mode_rel : B.srel U32.t =
  fun i0 i1 ->
    ((FStar.Seq.length i0 = 1 /\ (FStar.Seq.index i0 0 = 0ul \/ FStar.Seq.index i0 0 = 1ul)) 
      ==> 
      FStar.Seq.length i1 = 1 /\ (FStar.Seq.index i1 0 = 0ul \/ FStar.Seq.index i1 0 = 1ul))

(**
  * Predicate describing that (the blinking mode) pointer
  * has been initialised with a value 0ul or 1ul. Properties
  * of monotonic state then ensure that in any subsequent 
  * state evolution the pointer remains valued at 0ul or 1ul.
  *)
noextract
let led_mode_initialised_pred : B.spred U32.t =
  fun i ->  FStar.Seq.length i = 1 /\
         (FStar.Seq.index i 0 = 0ul \/ FStar.Seq.index i 0 = 1ul)

noextract
let led_mode_initialised (p:B.mpointer U32.t led_mode_rel led_mode_rel) : Type0 =
  B.witnessed p led_mode_initialised_pred

(**
  * A preorder that governs how the pointer we use to track the
  * status of the LED is allowed to evolve: once initialised
  * with value 0ul or 1ul, it can never go beyond these values.
  *)
noextract
let led_status_rel : B.srel U32.t =
  fun i0 i1 ->
    ((FStar.Seq.length i0 = 1 /\ (FStar.Seq.index i0 0 = 0ul \/ FStar.Seq.index i0 0 = 1ul)) 
      ==> 
      FStar.Seq.length i1 = 1 /\ (FStar.Seq.index i1 0 = 0ul \/ FStar.Seq.index i1 0 = 1ul))

(**
  * Predicate describing that (the LED status) pointer has
  * been initialised with a value 0ul or 1ul. Properties
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
  * The precondition of `set_led_mode`, it requires that:
  * - the given void pointer is an upcast of an `uint32_t` pointer 
  *   with `led_mode_rel` preorder,
  * - the given void pointer is live,
  * - the given void pointer is disjoint from the ghost state, and
  * - the given void pointer has once been initialised with 0 or 1.
  *)
noextract
let set_led_mode_pre (led_mode: VP.t) (h0: HS.mem) : GTot Type0 =
  led_mode `VP.is_upcast_of` led_mode_rel /\ 
  B.live h0 (VP.g_downcast led_mode_rel led_mode) /\
  isr_disjoint_from (VP.g_downcast led_mode_rel led_mode) /\
  led_mode_initialised (VP.g_downcast led_mode_rel led_mode)

(**
  * The postcondition of `set_led_mode`, it ensures that:
  * - the `uint32_t` value of the given void pointer remains 0ul or 1ul, and
  * - the function only modifies the given void pointer.
  *)
noextract
let set_led_mode_post (led_mode: VP.t) (h0: HS.mem) (_: unit) (h1: HS.mem)
    : GTot Type0 =
  led_mode `VP.is_upcast_of` led_mode_rel /\
  B.modifies (B.loc_buffer (VP.g_downcast led_mode_rel led_mode)) h0 h1

(**
  * Two auxiliary lemmas proving that after changing the void pointer 
  * in `set_led_mode`, it remains assigned the value 0ul or 1ul. 
  *)
noextract
let logand_add_lemma0 (x: U32.t)
    : Lemma (requires (x = 0ul))
            (ensures (U32.logand (x `U32.add` 1ul) 1ul = 1ul))
            [SMTPat (U32.logand (x `U32.add` 1ul) 1ul)] =
  assert (x `U32.add` 1ul = 1ul);
  assert (U32.logand 1ul 1ul = 1ul)

noextract
let logand_add_lemma1 (x: U32.t)
    : Lemma (requires (x = 1ul))
            (ensures (U32.logand (x `U32.add` 1ul) 1ul = 0ul))
            [SMTPat (U32.logand (x `U32.add` 1ul) 1ul)] =
  assert (x `U32.add` 1ul = 2ul);
  assert (U32.logand 2ul 1ul = 0ul)

(**
  * Interrupt handler code that changes the LED blinking 
  * mode between slow (`led_mode` points to `0ul`) or 
  * fast (`led_mode` points to `1ul`).
  *)
noextract
inline_for_extraction
let set_led_mode_espst (led_mode: VP.t)
    : ESPST unit (requires (set_led_mode_pre led_mode))
                 (ensures (set_led_mode_post led_mode)) =
  recall isr_map;
  let led = VPU32.downcast led_mode_rel led_mode in
  recall_p led led_mode_initialised_pred;
  led *= U32.logand (!*led `U32.add` 1ul) 1ul

let set_led_mode (led_status: VP.t)
    : ESPST_Extract unit (requires (set_led_mode_pre led_status))
                         (ensures (set_led_mode_post led_status)) =
  extract_st (fun _ -> set_led_mode_espst led_status)

(**
  * The precondition of `main_task`, it requires that:
  * - the GPIO-internals are live in the initial memory,
  * - `led_mode` is an upcast of an `uint32_t` pointer,
  * - `led_mode` is live in the initial memory,
  * - `led_mode` is disjoint from the ghost state, 
  * - `led_mode` has been witnessed to have been initialised,
  * - `led_status` is an upcast of an `uint32_t` pointer,
  * - `led_status` is live in the initial memory,
  * - `led_status` is disjoint from the ghost state, and
  * - `led_status` has been witnessed to have been initialised.  
  *)
noextract
let main_task_pre (led_mode: VP.t) (led_status:VP.t) (h0: HS.mem) : GTot Type0 =
  B.live h0 gpio_intl_bufs /\
  (* `led_mode` properties *)
  led_mode `VP.is_upcast_of` led_mode_rel /\ 
  B.live h0 (VP.g_downcast led_mode_rel led_mode) /\
  isr_disjoint_from (VP.g_downcast led_mode_rel led_mode)/\
  led_mode_initialised (VP.g_downcast led_mode_rel led_mode) /\
  (* `led_status` properties *)
  led_status `VP.is_upcast_of` led_status_rel /\ 
  B.live h0 (VP.g_downcast led_status_rel led_status) /\
  isr_disjoint_from (VP.g_downcast led_status_rel led_status) /\
  led_status_initialised (VP.g_downcast led_status_rel led_status)

(**
  * The postcondition `main_task`, it ensures that:
  * - the function only modifies only the GPIO-internals and `led_status`, and
  * - the function does not modify the ghost state.
  *)
noextract
let main_task_post (led_mode: VP.t) (led_status:VP.t) (h0: HS.mem) (_: unit) (h1: HS.mem) 
    : GTot Type0 =
  led_status `VP.is_upcast_of` led_status_rel /\
  modifies_gpio_intl_bufs_plus h0 h1 (B.loc_buffer (VP.g_downcast led_status_rel led_status)) /\ 
  isr_unmodified h0 h1

(**
  * A function that gets run in an infinite loop, and
  * which sets the LED blinking mode (to slow or fast)
  * depending on the value of `led_mode` which is
  * changed by the interrupt handler `set_led_mode`.
  *)
noextract
inline_for_extraction
let main_task_espst (led_mode: VP.t) (led_status:VP.t)
    : ESPST unit (requires (main_task_pre led_mode led_status)) 
                 (ensures (main_task_post led_mode led_status)) =
  recall isr_map;
  let led_mode = VPU32.downcast led_mode_rel led_mode in
  let led_status = VPU32.downcast led_status_rel led_status in

  recall_p led_mode led_mode_initialised_pred;
  recall_p led_status led_status_initialised_pred;
  
  let delay = ((100ul `U32.add` ((1ul `U32.sub` !*led_mode) `U32.mul` 400ul)) 
                `U32.div` ESP.portTICK_PERIOD_MS) in
  led_status *= U32.logand (!*led_status `U32.add` 1ul) 1ul;
  let _ = gpio_set_level led_gpio !*led_status in
  
  ESP.vTaskDelay delay

let main_task (led_mode: VP.t) (led_status:VP.t) 
    : ESPST_Extract unit (requires (main_task_pre led_mode led_status)) 
                         (ensures (main_task_post led_mode led_status)) =
  extract_st (fun _ -> main_task_espst led_mode led_status)

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
  * The main function, it:
  * - allocates a void pointer to track GPIO button pushes, 
  * - sets up a GPIO button configuration,
  * - installs an ISR handler, and
  * - in an infinite loop it polls for any button pushes so
  *   as to change the blinking mode of the LED.
  *)
noextract
inline_for_extraction
let app_main_espst (_: unit) 
    : ESPST unit (requires app_main_pre) (ensures app_main_post) =
  recall isr_map;
  
  // led status setup
  let led_mode = mmalloc #U32.t #led_status_rel HS.root 0ul in
  witness_p led_mode led_mode_initialised_pred;
  let _ = gpio_pad_select_gpio led_gpio in
  let _ = gpio_set_direction led_gpio gpio_mode_output in

  // button setup
  let _ = gpio_pad_select_gpio button_gpio in
  let _ = gpio_set_direction button_gpio gpio_mode_input in
  
  // isr install
  let _ = gpio_install_isr_service esp_intr_flag_lowmed in
  let _ =
    gpio_isr_handler_add 
      #set_led_mode_pre
      #set_led_mode_post
      button_gpio
      set_led_mode
      (VPU32.upcast led_mode_rel led_mode)
  in
  let _ = gpio_set_intr_type button_gpio gpio_intr_posedge in

  let led_status = mmalloc #U32.t #led_status_rel HS.root 0ul in
  witness_p led_status led_status_initialised_pred;

  // while loop
  VPW.while_true2 
    #main_task_pre 
    #main_task_post 
    main_task 
    (VPU32.upcast led_mode_rel led_mode) 
    (VPU32.upcast led_status_rel led_status)
  
  // isr uninstall
  // If we were to remove the infinite while loop, or have a terminating
  // loop in the code instead, we would also need to uninstall the 
  // installed ISR handlers so as to release resources (with `pop_frame`
  // in this case). This can be done by running the function given below:
  //
  // gpio_uninstall_isr_service ()



(**
  * Top-level main function that will get extracted to C.
  *)
let app_main (_: unit) 
    : ESPST_Extract unit (requires app_main_pre) (ensures app_main_post) =
  extract_st app_main_espst
