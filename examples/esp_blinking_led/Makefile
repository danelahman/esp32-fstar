include Makefile.include

KRML = $(KREMLIN_HOME)/krml

LIB_DIR = ../../lib
SRC_DIR = src
EXTRACT_DIR = dist

ESP_IDF = $(HOME)/esp/esp-idf
ESP_DIR = esp

ESP_PORT = /dev/ttyUSB0

.PHONY: all extract compile clean flash

all: extract compile flash

extract:
	mkdir -p $(EXTRACT_DIR)
	rm -f $(EXTRACT_DIR)/*.h
	rm -f $(EXTRACT_DIR)/*.c
	cd $(SRC_DIR) && \
	$(KRML) \
	  -I ../$(LIB_DIR) \
	  -tmpdir ../$(EXTRACT_DIR) \
	  -warn-error @4@5@18+9 \
	  -fparentheses \
	  -skip-compilation \
	  -skip-makefiles \
	  -minimal \
	  -bundle FStar.*,LowStar.*,Prims \
	  -add-include '"ESP_Types.h"' \
	  -add-include '"GPIO_Types.h"' \
	  -add-include '"Monotonic_VoidPointer.h"' \
	  -verify \
	  Main.fst
	rm -f $(EXTRACT_DIR)/WasmSupport.*
	rm -f $(EXTRACT_DIR)/C_Loops.*
	rm -f $(EXTRACT_DIR)/out.krml

compile:
	rm -f $(ESP_DIR)/main/*.h
	rm -f $(ESP_DIR)/main/*.c
	cp $(LIB_DIR)/c/* $(ESP_DIR)/main/
	cp $(EXTRACT_DIR)/* $(ESP_DIR)/main/
	cp $(SRC_DIR)/c/* $(ESP_DIR)/main/
	cd $(ESP_DIR) && \
	  . $(ESP_IDF)/export.sh && \
	  idf.py build

flash:
	cd $(ESP_DIR) && \
	  . $(ESP_IDF)/export.sh && \
	  idf.py -p $(ESP_PORT) flash monitor

clean:
	rm -f $(ESP_DIR)/main/*.h
	rm -f $(ESP_DIR)/main/*.c
	rm -f $(ESP_DIR)/sdkconfig
	cd $(ESP_DIR) && \
	  . $(ESP_IDF)/export.sh && \
	  idf.py fullclean
