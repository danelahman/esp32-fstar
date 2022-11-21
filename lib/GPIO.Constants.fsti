(**
  * This module exposes types and constants native to GPIO 
  * libraries. The C implementation can be found in c/GPIO.c.
  *)
module GPIO.Constants

module B = LowStar.Buffer

open FStar.Ghost

(**
  * Assumed buffer space modelling GPIO-internal variables.
  *
  * This assumption is just a modelling gadget. If one were to 
  * implement the currently assumed GPIO-specific functions, 
  * `gpio_intl_bufs` would be replaced with the actual buffers
  * used in that implementation.
  *)
noextract
val gpio_loc_t:Type0

val gpio_intl_bufs:B.buffer gpio_loc_t

(**
  * ESP and GPIO specific types and constants.
  *)
val esp_err_t:eqtype
val esp_err_esp_ok:esp_err_t
val esp_err_esp_fail:esp_err_t
val esp_err_esp_err_no_mem:esp_err_t
val esp_err_esp_err_invalid_arg:esp_err_t
val esp_err_esp_err_invalid_state:esp_err_t
val esp_err_esp_err_not_found:esp_err_t

val gpio_num_t:eqtype
val gpio_num_0:gpio_num_t
val gpio_num_5:gpio_num_t

val gpio_mode_t:eqtype
val gpio_mode_input:gpio_mode_t
val gpio_mode_output:gpio_mode_t

val esp_intr_flag_t:eqtype
val esp_intr_flag_lowmed:esp_intr_flag_t

val esp_intr_type_t:eqtype
val gpio_intr_posedge:esp_intr_type_t


(**
  * Logical specifications concerning the constants given above. 
  *)

(** Specifying which GPIO pins are inputs and which are outputs. *)
noextract
val gpio_num_is_input:gpio_num_t -> Type0
noextract
val gpio_num_is_output:gpio_num_t -> Type0

noextract
val gpio_nums_that_are_input : (gpio_num: gpio_num_t) -> 
  Lemma (requires (gpio_num == gpio_num_0 \/ 
                   gpio_num == gpio_num_5))
        (ensures  (gpio_num_is_input gpio_num))
  [SMTPat (gpio_num_is_input gpio_num)]

noextract
val gpio_nums_that_are_output : (gpio_num: gpio_num_t) -> 
  Lemma (requires (gpio_num == gpio_num_0 \/ 
                   gpio_num == gpio_num_5))
        (ensures  (gpio_num_is_output gpio_num))
  [SMTPat (gpio_num_is_output gpio_num)]


(** Specifying GPIO pins and I/O mode compatibility. *)
noextract
val gpio_num_mode_compat:gpio_num_t -> gpio_mode_t -> Type0

noextract
val gpio_num_mode_compat_input : (gpio_num: gpio_num_t) ->
  Lemma (requires (gpio_num_is_input gpio_num))
        (ensures  (gpio_num_mode_compat gpio_num gpio_mode_input))
  [SMTPat (gpio_num_mode_compat gpio_num gpio_mode_input)]

noextract
val gpio_num_mode_compat_output : (gpio_num: gpio_num_t) ->
  Lemma (requires (gpio_num_is_output gpio_num))
        (ensures  (gpio_num_mode_compat gpio_num gpio_mode_output))
  [SMTPat (gpio_num_mode_compat gpio_num gpio_mode_output)]
