module Main.Failure.Demo

module B = LowStar.Buffer
module U32 = FStar.UInt32

module HS = FStar.HyperStack
module MHS = FStar.Monotonic.HyperStack

open LowStar.BufferOps

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
let led_status_rel : B.srel U32.t =
  fun i0 i1 ->
    ((FStar.Seq.length i0 = 1 /\ (FStar.Seq.index i0 0 = 0ul \/ FStar.Seq.index i0 0 = 1ul)) 
      ==> 
      FStar.Seq.length i1 = 1 /\ (FStar.Seq.index i1 0 = 0ul \/ FStar.Seq.index i1 0 = 1ul))

(**
  * Predicate describing that (the LED status) pointer
  * has been initialised with a value 0ul or 1ul. Properties
  * of monotonic state then ensure that in any subsequent 
  * state evolution the pointer remains valued at 0ul or 1ul.
  *)
let led_status_initialised_pred : B.spred U32.t =
  fun i ->  FStar.Seq.length i = 1 /\
         (FStar.Seq.index i 0 = 0ul \/ FStar.Seq.index i 0 = 1ul)

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
let set_led_status_post (led_status: VP.t) (h0: HS.mem) (_: unit) (h1: HS.mem)
    : GTot Type0 =
  led_status `VP.is_upcast_of` led_status_rel /\
  B.modifies (B.loc_buffer (VP.g_downcast led_status_rel led_status)) h0 h1

(**
  * Two auxiliary lemmas proving that after changing the void pointer 
  * in `set_led_status`, it remains assigned the value 0ul or 1ul. 
  *)
let set_led_status_lemma0 (x: U32.t)
    : Lemma (requires (x = 0ul))
      (ensures (U32.logand (x `U32.add` 1ul) 1ul = 1ul))
      [SMTPat (U32.logand (x `U32.add` 1ul) 1ul)] =
  assert (x `U32.add` 1ul = 1ul);
  assert (U32.logand 1ul 1ul = 1ul)

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
let app_main_pre (h0: HS.mem) : GTot Type0 = 
  B.live h0 gpio_intl_bufs /\ 
  ~(isr_installed h0)

(** 
  * The postcondition of `app_main`, it ensures that:
  * - the function only modifies GPIO-internals and the ghost
  *   state modelling arguments/resources to ISR handlers.
  *)
let app_main_post (h0: HS.mem) (_: unit) (h1: HS.mem) : GTot Type0 = 
  modifies_gpio_intls h0 h1



(**
  * Examples of buggy main functions that are expected to fail.
  * The causes of failures are documented in comments below.
  *
  * As these examples are marked with the `expect_failure`
  * attribute, the typechecking of this buggy code succeeds.
  *)

[@expect_failure]
let app_main_failure1 (_: unit) 
    : ESPST unit (requires app_main_pre) (ensures app_main_post) =
  recall isr_map;
  
  // led setup
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
    gpio_isr_handler_add #set_led_status_pre
      #set_led_status_post
      button_gpio
      set_led_status
      (VPU32.upcast led_status_rel led_status)
  in
  let _ = gpio_set_intr_type button_gpio gpio_intr_posedge in

  led_status *= 42ul; // Failure: Trying to assign led_status a value (outside of the ISR
                      // handler) that invalidates its invariant of being values 0ul or 1ul.

  // while loop
  VPW.while_true #main_task_pre #main_task_post main_task (VPU32.upcast led_status_rel led_status)


[@expect_failure]
let app_main_failure2 (_: unit) 
    : ESPST unit (requires app_main_pre) (ensures app_main_post) =
  recall isr_map;
  
  // led setup
  let led_status = mmalloc #U32.t #led_status_rel HS.root 0ul in
  witness_p led_status led_status_initialised_pred;
  let _ = gpio_pad_select_gpio led_gpio in
  let _ = gpio_set_direction led_gpio gpio_mode_output in

  // button setup
  let _ = gpio_pad_select_gpio button_gpio in
  let _ = gpio_set_direction button_gpio gpio_mode_input in
  
  // isr install
  let _ = gpio_install_isr_service esp_intr_flag_lowmed in
  let _ = gpio_set_intr_type button_gpio gpio_intr_posedge in 
    // Failure: Trying to set the interrupt type without having
    //          installed the corresponding ISR handler.

  // while loop
  VPW.while_true #main_task_pre #main_task_post main_task (VPU32.upcast led_status_rel led_status)


[@expect_failure]
let app_main_failure3 (_: unit) 
    : ESPST unit (requires app_main_pre) (ensures app_main_post) =
  recall isr_map;
  
  // led setup
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
    gpio_isr_handler_add #set_led_status_pre
      #set_led_status_post
      button_gpio
      set_led_status
      (VPU32.upcast led_status_rel led_status)
  in
  let _ = gpio_set_intr_type button_gpio gpio_intr_posedge in

  // while loop
  //VPW.while_true #main_task_pre #main_task_post main_task (VPU32.upcast led_status_rel led_status);

  free led_status
    // Failure: With the infinite loop commented out, the program terminates 
    //          without uninstalling previously installed ISR handlers while
    //          deallocating the arguments/resources assigned to them.


let app_main_failure3_fixed (_: unit) 
    : ESPST unit (requires app_main_pre) (ensures app_main_post) =
  recall isr_map;
  
  // led setup
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
    gpio_isr_handler_add #set_led_status_pre
      #set_led_status_post
      button_gpio
      set_led_status
      (VPU32.upcast led_status_rel led_status)
  in
  let _ = gpio_set_intr_type button_gpio gpio_intr_posedge in

  // while loop
  //VPW.while_true #main_task_pre #main_task_post main_task (VPU32.upcast led_status_rel led_status);

  gpio_uninstall_isr_service (); // Fixing `app_main_failure3` by manually 
                                 // uninstalling all the installed ISR handlers.

  free led_status
