/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /Users/danel/KaRaMeL/krml -I ../../../lib -tmpdir ../dist -warn-error +2@4@5@18+9 -fparentheses -skip-compilation -skip-makefiles -minimal -bundle FStar.*,LowStar.*,Prims -add-include "ESP_Macros.h" -add-include "ESP_Types.h" -add-include "GPIO_Types.h" -add-include "Monotonic_VoidPointer.h" -verify Main.fst
  F* version: 9086005c
  KaRaMeL version: 6dd219f4
 */

#ifndef __GPIO_Constants_H
#define __GPIO_Constants_H




#include "ESP_Macros.h"
#include "ESP_Types.h"
#include "GPIO_Types.h"
#include "Monotonic_VoidPointer.h"
extern GPIO_Constants_gpio_loc_t *GPIO_Constants_gpio_intl_bufs;

extern GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_ok;

extern GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_fail;

extern GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_err_no_mem;

extern GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_err_invalid_arg;

extern GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_err_invalid_state;

extern GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_err_not_found;

extern GPIO_Constants_gpio_num_t GPIO_Constants_gpio_num_0;

extern GPIO_Constants_gpio_num_t GPIO_Constants_gpio_num_5;

extern GPIO_Constants_gpio_mode_t GPIO_Constants_gpio_mode_input;

extern GPIO_Constants_gpio_mode_t GPIO_Constants_gpio_mode_output;

extern GPIO_Constants_esp_intr_flag_t GPIO_Constants_esp_intr_flag_lowmed;

extern GPIO_Constants_esp_intr_type_t GPIO_Constants_gpio_intr_posedge;


#define __GPIO_Constants_H_DEFINED
#endif
