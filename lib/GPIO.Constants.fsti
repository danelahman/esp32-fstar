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

