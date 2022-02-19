#include "ESP.h"

/// Implementation of ESP.fsti::vTaskDelay
inline void ESP_vTaskDelay(ESP_tick_type_t ticks) {
    vTaskDelay(ticks);
}

ESP_tick_type_t ESP_portTICK_PERIOD_MS = portTICK_PERIOD_MS;
