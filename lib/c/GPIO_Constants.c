#include "driver/gpio.h"

#include "GPIO_Constants.h"


GPIO_Constants_gpio_num_t GPIO_Constants_gpio_num_0 = GPIO_NUM_0;
GPIO_Constants_gpio_num_t GPIO_Constants_gpio_num_5 = GPIO_NUM_5;

GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_ok = ESP_OK;
GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_fail = ESP_FAIL;
GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_no_mem = ESP_ERR_NO_MEM;
GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_invalid_arg = ESP_ERR_INVALID_ARG;
GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_invalid_state = ESP_ERR_INVALID_STATE;
GPIO_Constants_esp_err_t GPIO_Constants_esp_err_esp_not_found = ESP_ERR_NOT_FOUND;

bool GPIO_Constants_eq_esp_err_t(GPIO_Constants_esp_err_t e1, GPIO_Constants_esp_err_t e2) {
  return (e1 == e2);
}

GPIO_Constants_gpio_mode_t GPIO_Constants_gpio_mode_input = GPIO_MODE_INPUT;
GPIO_Constants_gpio_mode_t GPIO_Constants_gpio_mode_output = GPIO_MODE_OUTPUT;

GPIO_Constants_esp_intr_flag_t GPIO_Constants_esp_intr_flag_lowmed = ESP_INTR_FLAG_LOWMED;

GPIO_Constants_esp_intr_type_t GPIO_Constants_gpio_intr_posedge = GPIO_INTR_POSEDGE;
