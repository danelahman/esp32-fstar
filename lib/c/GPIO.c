#include "driver/gpio.h"

#include "GPIO.h"

inline GPIO_Constants_esp_err_t GPIO_gpio_set_level(GPIO_Constants_gpio_num_t num, uint32_t lv) {
    return gpio_set_level(num, lv);
}

inline GPIO_Constants_esp_err_t GPIO_gpio_pad_select_gpio(GPIO_Constants_gpio_num_t num) {
    gpio_pad_select_gpio(num);
    return 0;
}

inline GPIO_Constants_esp_err_t GPIO_gpio_set_direction(GPIO_Constants_gpio_num_t num, GPIO_Constants_gpio_mode_t mode) {
    return gpio_set_direction(num, mode);
}

inline GPIO_Constants_esp_err_t GPIO_gpio_install_isr_service(GPIO_Constants_esp_intr_flag_t flags) {
    return gpio_install_isr_service(flags);
}

inline void GPIO_gpio_uninstall_isr_service() {
    return gpio_uninstall_isr_service ();
}

inline GPIO_Constants_esp_err_t GPIO_gpio_set_intr_type(GPIO_Constants_gpio_num_t num, GPIO_Constants_esp_intr_type_t intr_type) {
    return gpio_set_intr_type(num, intr_type);
}

inline GPIO_Constants_esp_err_t GPIO_gpio_isr_handler_add(GPIO_Constants_gpio_num_t num, void (*handler)(Monotonic_VoidPointer_t), Monotonic_VoidPointer_t arg) {
    return gpio_isr_handler_add(num, handler, arg);
};
