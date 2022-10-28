#include "krmlinit.h"
#include "Main.h"

void app_main(void) {
    krmlinit_globals();
    Main_app_main();
}
