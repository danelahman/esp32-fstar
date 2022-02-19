/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: /Users/danel/KreMLin/krml -I ../../../lib -tmpdir ../dist -warn-error @4@5@18+9 -fparentheses -skip-compilation -skip-makefiles -minimal -bundle FStar.*,LowStar.*,Prims -add-include "ESP_Types.h" -add-include "GPIO_Types.h" -add-include "Monotonic_VoidPointer.h" -verify Main.fst
  F* version: 4d3b33f6
  KreMLin version: c113d20b
 */

#ifndef __VoidPointer_UInt32_H
#define __VoidPointer_UInt32_H
#include "ESP_Types.h"
#include "GPIO_Types.h"
#include "Monotonic_VoidPointer.h"


#include "Monotonic_VoidPointer_UInt32.h"

Monotonic_VoidPointer_t VoidPointer_UInt32_upcast(uint32_t *p);

uint32_t *VoidPointer_UInt32_downcast(Monotonic_VoidPointer_t p);


#define __VoidPointer_UInt32_H_DEFINED
#endif
