(**
  * This module exposes types and values native to ESP.
  * The C implementation can be found in c/ESP.c.
  *)

module ESP

open ESPST

module U32 = FStar.UInt32

noextract
type tick_type_t = U32.t

(**
  * portTICK_PERIOD_MS is an integer that we have to use
  * as divisor when calculating the amount of time to
  * sleep. Must be different from zero.
  *)
val portTICK_PERIOD_MS:n: tick_type_t{U32.v n <> 0}

(**
  * vTaskDelay is the function that actually makes the
  * program sleep. As of now, we know that the initial
  * memory has to be the same as the final one.
  *)
val vTaskDelay (num: tick_type_t)
    : ESPST unit (requires (fun h0 -> True)) (ensures (fun h0 r h1 -> h0 == h1))
