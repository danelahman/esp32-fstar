/* 
  This file was generated by KaRaMeL <https://github.com/FStarLang/karamel>
  KaRaMeL invocation: /Users/danel/KaRaMeL/krml -I ../../../lib -tmpdir ../dist -warn-error +2@4@5@18+9 -fparentheses -skip-compilation -skip-makefiles -minimal -bundle FStar.*,LowStar.*,Prims -add-include "ESP_Macros.h" -add-include "ESP_Types.h" -add-include "GPIO_Types.h" -add-include "Monotonic_VoidPointer.h" -verify Main.fst
  F* version: 9086005c
  KaRaMeL version: ad5e933b
 */

#ifndef __krmlinit_H
#define __krmlinit_H



#include "Main.h"
#include "GPIO_Constants.h"
#include "ESP_Macros.h"
#include "ESP_Types.h"
#include "GPIO_Types.h"
#include "Monotonic_VoidPointer.h"

#if defined(__GNUC__) && !(defined(_WIN32) || defined(_WIN64))
__attribute__ ((visibility ("hidden")))
#endif


void krmlinit_globals();


#define __krmlinit_H_DEFINED
#endif
