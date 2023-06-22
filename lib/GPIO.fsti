(**
  * Interface to various functions native to GPIO libraries.
  *)

module GPIO

open GPIO.Constants

module B = LowStar.Buffer
module VP = VoidPointer
open LowStar.BufferOps

module U32 = FStar.UInt32

module HS = FStar.HyperStack
module MHS = FStar.Monotonic.HyperStack

open ESPST

open FStar.Ghost

module M = FStar.Map

(**
  * Predicates concerning the buffer space modelling GPIO-internal variables.
  *)
noextract
let disjoint_from_gpio_intl_bufs #a #rel (p: B.mpointer a rel rel) : GTot Type0 = 
  B.disjoint gpio_intl_bufs p

noextract
let modifies_gpio_intl_bufs (h0 h1: HS.mem) : GTot Type0 =
  B.modifies (B.loc_buffer gpio_intl_bufs) h0 h1

noextract
let modifies_gpio_intl_bufs_plus (h0 h1: HS.mem) (l: B.loc) : GTot Type0 =
  B.modifies (B.loc_union (B.loc_buffer gpio_intl_bufs) l) h0 h1

noextract
let modifies_gpio_intls (h0 h1: HS.mem) : GTot Type0 =
  B.modifies (B.loc_union (B.loc_buffer gpio_intl_bufs) (B.loc_mreference isr_map)) h0 h1

noextract
let modifies_gpio_intls_plus (h0 h1: HS.mem) (l:B.loc) : GTot Type0 =
  B.modifies (B.loc_union (B.loc_union (B.loc_buffer gpio_intl_bufs) (B.loc_mreference isr_map)) l) h0 h1

(**
  * GPIO-specific functions. 
  *
  * They uniformly require that the GPIO-internal variables 
  * are live before calling the functions, and ensure that 
  * the functions only modify the GPIO-internal variables.
  * 
  * Some of the function signatures require additional 
  * pre-conditions to hold, so as to rule out possible errors
  * detailed in the corresponding ESP-IDF documentation. See
  * 
  *   https://docs.espressif.com/projects/esp-idf/en/latest/esp32/api-reference/peripherals/gpio.html
  * 
  * for the official documentation of these GPIO/ESP functions.
  *)

(** 
  * GPIO set output level. 
  *
  * Additionally requires that:
  * - The GPIO pin supports output mode.
  *
  * Additionally ensures that:
  * - No errors occur. The possible error ESP_ERR_INVALID_ARG is 
  *   ruled out due to function argument having to be a GPIO pin
  *   supporting output mode.
  * - The ISR handler service state and the GPIO pins to interrupt 
  *   handlers mapping remain unchanged.
  *)
val gpio_set_level (gpio_num: gpio_num_t) (level: U32.t)
    : ESPST esp_err_t
      (requires (fun h0 -> 
        B.live h0 gpio_intl_bufs /\ 
        gpio_num_is_output gpio_num))
      (ensures (fun h0 r h1 -> 
        modifies_gpio_intl_bufs h0 h1 /\ 
        r == esp_err_esp_ok /\
        isr_unmodified h0 h1))

(** 
  * Configure IO Pad as General Purpose IO. 
  * 
  * Additionally ensures that:
  * - No errors occur. The possible errors are ruled out due to
  *   function arguments having to be GPIO pins.
  * - The ISR handler service state and the GPIO pins to interrupt 
  *   handlers mapping remain unchanged.
  *)
val gpio_pad_select_gpio (gpio_num: gpio_num_t)
    : ESPST esp_err_t
      (requires (fun h0 -> 
        B.live h0 gpio_intl_bufs))
      (ensures (fun h0 r h1 -> 
        modifies_gpio_intl_bufs h0 h1 /\ 
        r == esp_err_esp_ok /\
        isr_unmodified h0 h1))

(** 
  * Configure GPIO direction, such as output_only, input_only, 
  * output_and_input. 
  *
  * Additionally requires that:
  * - The I/O mode is compatible with the given GPIO pin.
  *
  * Additionally ensures that:
  * - No errors occur. The possible error ESP_ERR_INVALID_ARG is 
  *   ruled out due the given mode having to be compatible with
  *   the given GPIO pin.
  * - The ISR handler service state and the GPIO pins to interrupt 
  *   handlers mapping remain unchanged.
  *)
val gpio_set_direction (gpio_num: gpio_num_t) (mode: gpio_mode_t)
    : ESPST esp_err_t
      (requires (fun h0 -> 
        B.live h0 gpio_intl_bufs /\
        gpio_num_mode_compat gpio_num mode))
      (ensures (fun h0 r h1 -> 
        modifies_gpio_intl_bufs h0 h1 /\ 
        r == esp_err_esp_ok /\
        isr_unmodified h0 h1))

(** 
  * Install the GPIO driver’s ETS_GPIO_INTR_SOURCE ISR handler 
  * service, which allows per-pin GPIO interrupt handlers. 
  *
  * Additionally requires that:
  * - The ISR service has not yet been installed.
  *
  * Additionally ensures that:
  * - ESP_ERR_INVALID_STATE and ESP_ERR_INVALID_ARG do not occur.
  * - If the function returns ESP_OK, then:
  *   - The ISR handler service gets installed.
  *   - The ISR handler service is initialised in an empty state.
  * - If the function does not return ESP_OK, then:
  *   - The ISR handler service state and the GPIO pins to interrupt 
  *     handlers mapping remain unchanged.
  *
  * Note: ESP_ERR_NO_MEM and ESP_ERR_NOT_FOUND errors can still potentially occur.
  *)
val gpio_install_isr_service (intr_flags: esp_intr_flag_t)
    : ESPST esp_err_t
      (requires (fun h0 -> 
        B.live h0 gpio_intl_bufs /\ 
        ~(isr_installed h0)))
      (ensures (fun h0 r h1 -> 
        modifies_gpio_intl_bufs h0 h1 /\ 
        r <> esp_err_esp_err_invalid_state /\
        r <> esp_err_esp_err_invalid_arg /\
        (r = esp_err_esp_ok \/
         r = esp_err_esp_err_no_mem \/
         r = esp_err_esp_err_not_found) /\
        (r = esp_err_esp_ok ==> isr_installed h1 /\ 
                               isr_empty h1) /\
        (r <> esp_err_esp_ok ==> isr_unmodified h0 h1)))

(** 
  * Uninstall the driver’s GPIO ISR service, freeing related 
  * resources. 
  *
  * Additionally requires that:
  * - The ISR handler service is installed.
  *
  * Additionally ensures that:
  * - The ISR service gets uninstalled.
  *)
val gpio_uninstall_isr_service (_: unit)
    : ESPST unit
      (requires (fun h0 -> 
        B.live h0 gpio_intl_bufs /\ 
        isr_installed h0))
      (ensures (fun h0 r h1 -> 
        modifies_gpio_intls h0 h1 /\ 
        ~(isr_installed h1)))

(** 
  * GPIO set interrupt trigger type. 
  *
  * Additionally requires that:
  * - The ISR handler service has an interrupt handler installed 
  *   for the given GPIO pin.
  *
  * Additionally ensures that:
  * - No errors occur. The possible error ESP_ERR_INVALID_ARG is 
  *   ruled out due the argument having to be a GPIO pin.
  * - The ISR handler service state and the GPIO pins to interrupt 
  *   handlers mapping remain unchanged.
  *)
val gpio_set_intr_type (gpio_num: gpio_num_t) (intr_type: esp_intr_type_t)
    : ESPST esp_err_t
      (requires (fun h0 -> 
        B.live h0 gpio_intl_bufs /\ 
        isr_contains h0 gpio_num))
      (ensures (fun h0 r h1 -> 
        modifies_gpio_intl_bufs h0 h1 /\ 
        r == esp_err_esp_ok /\
        isr_unmodified h0 h1))

(**
  * Function for installing ISR handlers. 
  *
  * In its precondition, the function requires that:
  * - the GPIO-internal variables are live, 
  * - the argument to the ISR handler is live,
  * - the given GPIO pin number does not yet have a handler installed,
  * - the precondition of the handler function holds (this ensures that
  *   any resources required by it have been allocated already), and
  * - the specification of the ISR handler is stable with respect to its
  *   possible state changes (being simimilar to a loop invariant).
  *
  * In its postcondition, the function ensures that:
  * - it only modify the GPIO-internal variables and the ghost state,
  * - the ghost state maps the given GPIO pin to the given argument/resource, and 
  * - no errors occur (the possible errors ESP_ERR_INVALID_ARG and 
  *   ESP_ERR_NOT_FOUND are ruled out by requiring the arguments to
  *   be well-typed, and for the ISR handler service to not yet have
  *   an interrupt handler installed for the given GPIO pin).
  *
  * Note: The pre- and postconditions are marked erased so as to ensure
  * they get erased during extraction to C.
  *)
val gpio_isr_handler_add
      (#pre: erased (VP.t -> st_pre))
      (#post: erased (p: VP.t -> h0: HS.mem -> st_post unit))
      (gpio_num: gpio_num_t)
      (isr_handler:
          (p: VP.t
              -> ESPST_Extract unit
                  (requires (fun h0 -> reveal pre p h0))
                  (ensures (fun h0 x h1 -> reveal post p h0 x h1))))
      (args: VP.t)
    : ESPST esp_err_t
      (requires
        (fun h0 ->
          B.live h0 gpio_intl_bufs /\    // GPIO internals must be live
          args `VP.is_live_in` h0 /\     // argument void pointer must be live
          isr_installed h0 /\            // ISR service must have been installed
          ~(isr_contains h0 gpio_num) /\ // no interrupt handler must have been installed for `gpio_num`
          reveal pre args h0 /\          // precondition of the interrupt handler must hold
          (forall h0 h1. reveal post args h0 () h1 ==> B.modifies (VP.loc_voidpointer args) h0 h1) /\
                                        // interrupt handler must modify only the explicitly given resources
          (forall h0 h1. reveal pre args h0 /\ reveal post args h0 () h1 ==> reveal pre args h1)))
      (ensures                          // interrupt handler has to satisfy a loop invariant
        (fun h0 r h1 -> 
          modifies_gpio_intls h0 h1 /\             // at most GPIO internals are modified
          r == esp_err_esp_ok /\                   // no errors occur
          isr_updated_with h0 h1 gpio_num args))  // ghost state is updated by mapping `gpio_num` to the argument void pointer
