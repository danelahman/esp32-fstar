/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /Users/danel/KaRaMeL/krml -I ../../../lib -tmpdir ../dist -warn-error +2@4@5@18+9 -fparentheses -skip-compilation -skip-makefiles -minimal -bundle FStar.*,LowStar.*,Prims -add-include "ESP_Macros.h" -add-include "ESP_Types.h" -add-include "GPIO_Types.h" -add-include "Monotonic_VoidPointer.h" -verify Main.fst
  F* version: 9086005c
  KaRaMeL version: 6dd219f4
 */

#ifndef __GPIO_H
#define __GPIO_H




#include "ESP_Macros.h"
#include "ESP_Types.h"
#include "GPIO_Types.h"
#include "Monotonic_VoidPointer.h"
extern GPIO_Constants_esp_err_t
GPIO_gpio_set_level(GPIO_Constants_gpio_num_t gpio_num, uint32_t level);

extern GPIO_Constants_esp_err_t GPIO_gpio_pad_select_gpio(GPIO_Constants_gpio_num_t gpio_num);

extern GPIO_Constants_esp_err_t
GPIO_gpio_set_direction(GPIO_Constants_gpio_num_t gpio_num, GPIO_Constants_gpio_mode_t mode);

extern GPIO_Constants_esp_err_t
GPIO_gpio_install_isr_service(GPIO_Constants_esp_intr_flag_t intr_flags);

extern void GPIO_gpio_uninstall_isr_service();

extern GPIO_Constants_esp_err_t
GPIO_gpio_set_intr_type(
  GPIO_Constants_gpio_num_t gpio_num,
  GPIO_Constants_esp_intr_type_t intr_type
);

extern GPIO_Constants_esp_err_t
GPIO_gpio_isr_handler_add(
  GPIO_Constants_gpio_num_t gpio_num,
  void (*isr_handler)(Monotonic_VoidPointer_t x0),
  Monotonic_VoidPointer_t args
);


#define __GPIO_H_DEFINED
#endif
