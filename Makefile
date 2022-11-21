EXAMPLES_DIR = examples

.PHONY: all

all: $(EXAMPLES_DIR)/*
	for file in $^ ; do \
                cd $${file} && \
		make extract && \
		make compile && \
		cd ../.. ; \
        done

