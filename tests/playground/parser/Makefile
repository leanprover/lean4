LEANC=../../../bin/leanc
LEAN=../../../bin/lean
SRCS = $(shell ls *.lean)
OLEANS = $(SRCS:.lean=.olean)
CPPS = $(SRCS:.lean=.cpp)
OBJS = $(SRCS:.lean=.o)
DEPS = $(SRCS:.lean=.depend)
CPPFLAGS = -O3

.PHONY: all clean

all: parser $(OLEANS)

depends: $(DEPS)

%.depend: %.lean
	@echo $(<:.lean=.olean): `$(LEAN) --deps $< | python relative.py` > $@

%.olean: %.lean %.depend
	$(LEAN) --make --cpp="$*.cpp.tmp" $<
	mv "$*.cpp.tmp" "$*.cpp"
	@touch $*.olean

%.cpp: %.olean
	@

%.o: %.cpp
	$(LEANC) -c $(CPPFLAGS) -o $@ $<

parser: $(OBJS)
	$(LEANC) -o parser $(OBJS)

clean:
	rm -f *.olean
	rm -f *.cpp
	rm -f *.o
	rm -f *.depend
	rm -f parser

include $(DEPS)
