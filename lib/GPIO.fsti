(**
  * This module exposes various functions native to GPIO 
  * libraries. The implementation can be found in c/GPIO.c
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
let disjoint_from_gpio_intl_bufs #a #rel (p: B.mpointer a rel rel) : GTot Type0 = 
  B.disjoint gpio_intl_bufs p

let modifies_gpio_intl_bufs (h0 h1: HS.mem) : GTot Type0 =
  B.modifies (B.loc_buffer gpio_intl_bufs) h0 h1

let modifies_gpio_intl_bufs_plus (h0 h1: HS.mem) (l: B.loc) : GTot Type0 =
  B.modifies (B.loc_union (B.loc_buffer gpio_intl_bufs) l) h0 h1

let modifies_gpio_intls (h0 h1: HS.mem) : GTot Type0 =
  B.modifies (B.loc_union (B.loc_buffer gpio_intl_bufs) (B.loc_mreference isr_map)) h0 h1

let modifies_gpio_intls_plus (h0 h1: HS.mem) (l:B.loc) : GTot Type0 =
  B.modifies (B.loc_union (B.loc_union (B.loc_buffer gpio_intl_bufs) (B.loc_mreference isr_map)) l) h0 h1

(**
  * GPIO-specific functions. Most of their specifications are
  * similar: requiring that the GPIO-internal variables are 
  * live before calling the functions, and ensurnig that the 
  * functions only modify the GPIO-internal variables and the 
  * ghost state modelling usage of ISR arguments/resources.
  *)
val gpio_set_level (gpio_num: gpio_num_t) (level: U32.t)
    : ESPST esp_err_t
      (requires (fun h0 -> B.live h0 gpio_intl_bufs))
      (ensures (fun h0 r h1 -> modifies_gpio_intl_bufs h0 h1 /\ isr_unmodified h0 h1))

val gpio_pad_select_gpio (gpio_num: gpio_num_t)
    : ESPST esp_err_t
      (requires (fun h0 -> B.live h0 gpio_intl_bufs))
      (ensures (fun h0 r h1 -> modifies_gpio_intl_bufs h0 h1 /\ isr_unmodified h0 h1))

val gpio_set_direction (gpio_num: gpio_num_t) (mode: gpio_mode_t)
    : ESPST esp_err_t
      (requires (fun h0 -> B.live h0 gpio_intl_bufs))
      (ensures (fun h0 r h1 -> modifies_gpio_intl_bufs h0 h1 /\ isr_unmodified h0 h1))

val gpio_install_isr_service (intr_flags: esp_intr_flag_t)
    : ESPST esp_err_t
      (requires (fun h0 -> B.live h0 gpio_intl_bufs /\ ~(isr_installed h0)))
      (ensures (fun h0 r h1 -> modifies_gpio_intl_bufs h0 h1 /\ isr_installed h1 /\ isr_empty h1))

val gpio_uninstall_isr_service (_: unit)
    : ESPST unit
      (requires (fun h0 -> B.live h0 gpio_intl_bufs /\ isr_installed h0))
      (ensures (fun h0 r h1 -> modifies_gpio_intls h0 h1 /\ ~(isr_installed h0)))

val gpio_set_intr_type (gpio_num: gpio_num_t) (intr_type: esp_intr_type_t)
    : ESPST esp_err_t
      (requires (fun h0 -> B.live h0 gpio_intl_bufs /\ isr_contains h0 gpio_num))
      (ensures (fun h0 r h1 -> modifies_gpio_intl_bufs h0 h1 /\ isr_unmodified h0 h1))

(**
  * Function for installing ISR handlers. 
  *
  * As a precondition, the function requires that:
  * - the GPIO-internal variables are live, 
  * - the argument to the ISR handler is live,
  * - the given GPIO pin number does not yet have a handler installed,
  * - the precondition of the handler function holds (this ensures that
  *   any resources required by it have been allocated already), and
  * - the specification of the ISR handler is stable with respect to its
  *   possible state changes (being simimilar to a loop invariant).
  *
  * As a postcondition, the function ensures that:
  * - it only modify the GPIO-internal variables and the ghost state, and
  * - the ghost state maps the given GPIO pin to the given argument/resource.
  *
  * The pre- and postconditions are marked erased so as to ensure they
  * get erased during extraction to C.
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
        (fun h0 x h1 -> 
          modifies_gpio_intls_plus h0 h1 (VP.loc_voidpointer args) /\ // at most GPIO internals and argument void pointer are modified
          isr_updated_with h0 h1 gpio_num args))                     // ghost state is updated by mapping `gpio_num` to the argument void pointer
