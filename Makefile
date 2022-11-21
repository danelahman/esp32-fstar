EXAMPLES_DIR = examples

.PHONY: examples

examples: $(EXAMPLES_DIR)/*
	for file in $^ ; do \
                cd $${file} && \
		make extract && \
		make compile && \
		cd ../.. ; \
        done

