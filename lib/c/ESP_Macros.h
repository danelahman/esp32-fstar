#ifndef __ESP_Macros_H
#define __ESP_Macros_H

/* TODO: Switch over to using KaRaMeL macros proper. */

#ifndef KRML_HOST_MALLOC
#  define KRML_HOST_MALLOC malloc
#endif

#ifndef KRML_HOST_CALLOC
#  define KRML_HOST_CALLOC calloc
#endif

#ifndef KRML_HOST_FREE
#  define KRML_HOST_FREE free
#endif

#define __ESP_Macros_H_DEFINED
#endif
