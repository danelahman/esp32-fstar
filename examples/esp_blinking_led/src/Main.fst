module Main

module B = LowStar.Buffer
module U32 = FStar.UInt32

module HS = FStar.HyperStack
module MHS = FStar.Monotonic.HyperStack

open GPIO.Constants
open GPIO
open ESPST

open LowStar.BufferOps

module VP = VoidPointer
module VPU32 = VoidPointer.UInt32
module VPW = VoidPointer.While

let blink_gpio = gpio_num_5
let button_gpio = gpio_num_0

(**
  * The precondition of `set_led_status`, it requires that:
  * - the given void pointer is an upcast of an uint32 pointer,
  * - the given void pointer is live,
  * - the given void pointer is disjoint from GPIO-internals,
  * - the given void pointer is disjoint from the ghost state, and
  * - the uint32 value of the given void pointer is 0ul or 1ul, so
  *   as to avoid overflow and wraparound in the computation.
  *)
let set_led_status_pre (led_status: VP.t) (h0: HS.mem) : GTot Type0=
  led_status `VP.is_upcast_of` U32.t /\ 
  B.live h0 (VP.g_downcast #U32.t led_status) /\
  disjoint_from_gpio_intl_bufs (VP.g_downcast #U32.t led_status) /\
  disjoint_from_isr (VP.g_downcast #U32.t led_status) /\
  (B.get h0 (VP.g_downcast #U32.t led_status) 0 = 0ul \/
    B.get h0 (VP.g_downcast #U32.t led_status) 0 = 1ul)

(**
  * The postcondition `set_led_status`, it ensures that:
  * - the uint32 value of the given void pointer remains 0ul or 1ul, and
  * - the function only modifies the given void pointer.
  *)
let set_led_status_post (led_status: VP.t) (h0: HS.mem) (_: unit) (h1: HS.mem)
    : GTot Type0 =
  led_status `VP.is_upcast_of` U32.t /\
  (B.get h1 (VP.g_downcast #U32.t led_status) 0 = 0ul \/
    B.get h1 (VP.g_downcast #U32.t led_status) 0 = 1ul) /\
  B.modifies (B.loc_buffer (VP.g_downcast #U32.t led_status)) h0 h1

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
  * Function that flips the value of the given void
  * pointer from 0ul to 1ul, and vice versa, resulting
  * in the associated LED being turned either on or off.
  *)
let set_led_status (led_status: VP.t)
    : ISRST unit
      (requires (set_led_status_pre led_status))
      (ensures (set_led_status_post led_status)) =
  recall isr_map;
  let led = VPU32.downcast led_status in
  led *= U32.logand (!*led `U32.add` 1ul) 1ul

(**
  * The precondition of `main_task`, it requires that:
  * - the given void pointer is an upcast of an uint32 pointer,
  * - the given void pointer is live,
  * - the GPIO-internals are live,
  * - the given void pointer is disjoint from GPIO-internals, and
  * - the given void pointer is disjoint from the ghost state.
  *)
let main_task_pre (led_status: VP.t) (h0: HS.mem) : GTot Type0 =
  led_status `VP.is_upcast_of` U32.t /\ 
  B.live h0 gpio_intl_bufs /\
  B.live h0 (VP.g_downcast #U32.t led_status) /\
  disjoint_from_gpio_intl_bufs (VP.g_downcast #U32.t led_status) /\
  disjoint_from_isr (VP.g_downcast #U32.t led_status)

(**
  * The postcondition `main_task`, it ensures that:
  * - the function only modifies only the GPIO-internals, and
  * - the function does not modify the ghost state.
  *)
let main_task_post (led_status: VP.t) (h0: HS.mem) (_: unit) (h1: HS.mem) 
    : GTot Type0=
  modifies_gpio_intl_bufs h0 h1 /\ isr_unmodified h0 h1

(**
  * A function that gets run in an infinite loop, 
  * and which sets the LED status (turning it on or off)
  * depending ono thee value of the given void pointer.
  *)
let main_task (led_status: VP.t)
    : ESPST unit (requires (main_task_pre led_status)) 
                 (ensures (main_task_post led_status)) =
  let _ = gpio_set_level blink_gpio !*(VPU32.downcast led_status) in
  ESP.vTaskDelay (100ul `U32.div` ESP.portTICK_PERIOD_MS)

(** 
  * The precondition of `app_main`, it requires that:
  * - the GPIO-internals are live, and
  * - that the ghost state is empty to begin with 
  *   (modelling that no ISR handlers have been installed).
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
  * The main function, it:
  * - allocates a void pointer to track GPIO button pushes, 
  * - sets up a GPIO button configuration,
  * - installs an ISR handler,
  * - in an infinite loop it polls for any button pushes so
  *   as to change the colour of the LED, and
  * - it uninstalls the ISR hander in the end (so as to ensure
  *   that popping the stack frame and discarding the void 
  *   pointer verifies the specification of the ESPST effect).
  *)
#set-options "--z3rlimit_factor 5"
let app_main (_: unit) 
    : ESPST unit (requires app_main_pre) (ensures app_main_post) =
  recall isr_map;

  push_frame ();
  
  // blinker setup
  let led_status = B.alloca 0ul 1ul in
  let _ = gpio_pad_select_gpio blink_gpio in
  let _ = gpio_set_direction blink_gpio gpio_mode_output in
  
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
      (VPU32.upcast led_status)
  in
  let _ = gpio_set_intr_type button_gpio gpio_intr_posedge in

  // while loop
  VPW.while_true #main_task_pre #main_task_post main_task (VPU32.upcast led_status);

  // isr uninstall
  // If we were to remove the infinite while loop, or have a terminating
  // loop in the code instead, we would also need to uninstall the 
  // installed ISR handlers so as to release resources (with `pop_frame`
  // in this case). This can be done by running the function given below:
  //
  // gpio_uninstall_isr_service ();
  
  pop_frame ()

