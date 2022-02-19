#include "Monotonic_VoidPointer_UInt32.h"


Monotonic_VoidPointer_t Monotonic_VoidPointer_UInt32_upcast(uint32_t *p) {
    return (Monotonic_VoidPointer_t) p;
}

uint32_t *Monotonic_VoidPointer_UInt32_downcast(Monotonic_VoidPointer_t p) {
    return (uint32_t*) p;
}
