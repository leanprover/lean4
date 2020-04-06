LEAN_BIN=$(LEAN_ROOT)/bin
LEAN=$(LEAN_BIN)/lean
LEANC=$(LEAN_BIN)/leanc
PROJECT_ROOT=.
SRCS = $(shell cd $(PROJECT_ROOT); find . -name '*.lean')
OUT ?= out
DEPS = $(addprefix $(OUT)/,$(SRCS:.lean=.depend))
OBJS = $(SRCS:.lean=.olean)
C_LEAN_OBJS = $(addprefix $(OUT)/,$(SRCS:.lean=.o))
ESC_OUT=$(subst /,\\/,$(OUT))
CPPFLAGS = -I$(HOME)/lean/lean4/src -O3
CPP_SRCS = myfuns.cpp
CPP_OBJS = $(addprefix $(OUT)/,$(CPP_SRCS:.cpp=.o))

.PHONY: all clean version dump_out

all: $(C_LEAN_OBJS) $(CPP_OBJS) $(OUT)/test

depends: $(DEPS)

$(OUT)/%.depend: %.lean
	@mkdir -p $(OUT)
	@ deps=`$(LEAN) --deps $< | python relative.py`; echo $(<:.lean=.olean): $$deps > $@

%.olean: %.lean $(addprefix $(OUT)/,%.depend)
	@echo "[    ] Building $<"
	@mkdir -p $(OUT)/$(*D)
	@LEAN_PATH=INI=$(LEAN_ROOT)/src/Init:Proj=$(PROJECT_ROOT) $(LEAN) --make --c="$(OUT)/$*.c.tmp" $<
	@mv "$(OUT)/$*.c.tmp" "$(OUT)/$*.c"
	@touch $@

$(OUT)/%.c: %.olean
	@

$(OUT)/%.o: $(OUT)/%.c
	@echo "[    ] Building $<"
	@mkdir -p "$(@D)"
	@ $(LEANC) -c -o $@ $< $(LEANC_OPTS) $(CPPFLAGS)

$(OUT)/%.o: %.cpp
	@echo "[    ] Building $<"
	@mkdir -p "$(@D)"
	@ $(LEANC) -c -o $@ $< $(LEANC_OPTS) $(CPPFLAGS)

$(OUT)/test: $(C_LEAN_OBJS) $(CPP_OBJS)
	@ $(LEANC) -o $(OUT)/test $(C_LEAN_OBJS) $(CPP_OBJS)

clean:
	rm -rf $(OUT) $(OBJS) $(C_LEAN_OBJS) $(CPP_OBJS) $(OUT)/test

version:
	$(LEAN) -v

.PRECIOUS: $(OUT)/%.depend $(OUT)/%.c

include $(DEPS)
