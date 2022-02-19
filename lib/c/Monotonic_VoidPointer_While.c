#include "Monotonic_VoidPointer_While.h"

void Monotonic_VoidPointer_While_while_true(void (*body)(Monotonic_VoidPointer_t),
                                            Monotonic_VoidPointer_t arg) {
  while (1) body(arg);
}

void Monotonic_VoidPointer_While_while_true2(void (*body)(Monotonic_VoidPointer_t,Monotonic_VoidPointer_t),
                                             Monotonic_VoidPointer_t arg1,Monotonic_VoidPointer_t arg2) {
  while (1) body(arg1,arg2);
}
