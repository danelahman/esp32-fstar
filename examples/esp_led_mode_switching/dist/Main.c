/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /Users/danel/KaRaMeL/krml -I ../../../lib -tmpdir ../dist -warn-error +2@4@5@18+9 -fparentheses -skip-compilation -skip-makefiles -minimal -bundle FStar.*,LowStar.*,Prims -add-include "ESP_Macros.h" -add-include "ESP_Types.h" -add-include "GPIO_Types.h" -add-include "Monotonic_VoidPointer.h" -verify Main.fst
  F* version: 9086005c
  KaRaMeL version: ad5e933b
 */

#include "Main.h"



GPIO_Constants_gpio_num_t Main_button_gpio;

GPIO_Constants_gpio_num_t Main_led_gpio;

void Main_set_led_mode(Monotonic_VoidPointer_t led_status)
{
  uint32_t *x1 = Monotonic_VoidPointer_UInt32_downcast(led_status);
  uint32_t x3 = *x1;
  uint32_t x30 = x3 + (uint32_t)1U;
  uint32_t x31 = x30 & (uint32_t)1U;
  *x1 = x31;
}

void Main_main_task(Monotonic_VoidPointer_t led_mode, Monotonic_VoidPointer_t led_status)
{
  uint32_t *x1 = Monotonic_VoidPointer_UInt32_downcast(led_mode);
  uint32_t *x2 = Monotonic_VoidPointer_UInt32_downcast(led_status);
  uint32_t x5 = *x1;
  uint32_t x50 = (uint32_t)1U - x5;
  uint32_t x51 = x50 * (uint32_t)400U;
  uint32_t x52 = (uint32_t)100U + x51;
  uint32_t x53 = x52 / ESP_portTICK_PERIOD_MS;
  uint32_t x6 = *x2;
  uint32_t x60 = x6 + (uint32_t)1U;
  uint32_t x61 = x60 & (uint32_t)1U;
  *x2 = x61;
  uint32_t x7 = *x2;
  GPIO_Constants_esp_err_t x70 = GPIO_gpio_set_level(Main_led_gpio, x7);
  ESP_vTaskDelay(x53);
}

void Main_app_main()
{
  uint32_t *x1 = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint32_t));
  GPIO_Constants_esp_err_t x3 = GPIO_gpio_pad_select_gpio(Main_led_gpio);
  GPIO_Constants_esp_err_t
  x4 = GPIO_gpio_set_direction(Main_led_gpio, GPIO_Constants_gpio_mode_output);
  GPIO_Constants_esp_err_t x5 = GPIO_gpio_pad_select_gpio(Main_button_gpio);
  GPIO_Constants_esp_err_t
  x6 = GPIO_gpio_set_direction(Main_button_gpio, GPIO_Constants_gpio_mode_input);
  GPIO_Constants_esp_err_t
  x7 = GPIO_gpio_install_isr_service(GPIO_Constants_esp_intr_flag_lowmed);
  Monotonic_VoidPointer_t x8 = Monotonic_VoidPointer_UInt32_upcast(x1);
  GPIO_Constants_esp_err_t
  x80 = GPIO_gpio_isr_handler_add(Main_button_gpio, Main_set_led_mode, x8);
  GPIO_Constants_esp_err_t
  x9 = GPIO_gpio_set_intr_type(Main_button_gpio, GPIO_Constants_gpio_intr_posedge);
  uint32_t *x10 = KRML_HOST_CALLOC((uint32_t)1U, sizeof (uint32_t));
  Monotonic_VoidPointer_t x12 = Monotonic_VoidPointer_UInt32_upcast(x1);
  Monotonic_VoidPointer_t x13 = Monotonic_VoidPointer_UInt32_upcast(x10);
  Monotonic_VoidPointer_While_while_true2(Main_main_task, x12, x13);
}

