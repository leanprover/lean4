# Copyright (c) 2018 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Simon Hudon, Sebastian Ullrich
LEAN ?= lean
SRCS = $(shell find . -name '*.lean')
OBJS = $(SRCS:.lean=.olean)
DEPS = $(SRCS:.lean=.depend)

.PHONY: all clean

all: $(OBJS)

depends: $(DEPS)

%.depend: %.lean
	@echo $(<:.lean=.olean): `$(LEAN) --deps $< | python relative.py` > $@

%.olean: %.lean %.depend
	$(LEAN) --make $<

clean:
	find . -name *.olean -delete
	find . -name *.depend -delete

.PRECIOUS: %.depend

include $(DEPS)
