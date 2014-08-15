TOP := $(dir $(lastword $(MAKEFILE_LIST)))
DIR := $(shell pwd)
LEAN_FILES := $(shell find $(DIR) -type f -name '*.lean')
OLEAN_FILES := $(LEAN_FILES:.lean=.olean)
ILEAN_FILES := $(LEAN_FILES:.lean=.ilean)
DEP_FILES := $(LEAN_FILES:.lean=.d)
LEAN_BIN_DIR := $(dir $(LEAN))
LEAN_VERSION_FILE := $(LEAN_BIN_DIR)version
LTAGS := $(LEAN_BIN_DIR)ltags

all: $(OLEAN_FILES) $(DEP_FILES)

%.olean: %.lean $(LEAN_VERSION_FILE)
	@rm -f $@
	$(LEAN) $(LEAN_OPTIONS) $< -o $@ -c $(@:.olean=.clean) -i $(@:.olean=.ilean)

%.d: %.lean $(LEAN_VERSION_FILE)
	@echo Making dependency file \'$@\' ...
	@rm -f $@
	@rm -f $@.tmp
	@$(LEAN) --deps $< > $@.tmp
	@printf "$(basename $@).olean : $< $@ " > $@
	@tr "\n" " " < $@.tmp >> $@
	@rm -f $@.tmp

%.ilean: %.lean %.olean $(LEAN_VERSION_FILE)
	$(LEAN) $(LEAN_OPTIONS) $< -i $@

etags tags: TAGS

TAGS: $(ILEAN_FILES)
	$(LTAGS)

-include $(LEAN_FILES:.lean=.d)

.PHONY: all clean tags etags gtags

clean:
	find . -type f -name "*.olean" -delete
	find . -type f -name "*.clean" -delete
	find . -type f -name "*.ilean" -delete
	find . -type f -name "*.d" -delete
