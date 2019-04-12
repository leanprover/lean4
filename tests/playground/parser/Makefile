LEANC=../../../bin/leanc
LEAN=../../../bin/lean
COMMON_SRCS = parser.lean syntax.lean filemap.lean
SRCS = $(COMMON_SRCS) test1.lean
OLEANS = $(SRCS:.lean=.olean)
CPPS = $(SRCS:.lean=.cpp)
COMMON_OBJS = $(COMMON_SRCS:.lean=.o)
DEPS = $(SRCS:.lean=.depend)
CPPFLAGS = -O3

.PHONY: all clean

all: test1 $(OLEANS)

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

test1: test1.o $(COMMON_OBJS)
	$(LEANC) -o $@ $^

# test2: test2.o $(COMMON_OBJS)
#	$(LEANC) -o $@ $^

clean:
	rm -f *.olean
	rm -f *.cpp
	rm -f *.o
	rm -f *.depend
	rm -f test1 test2

.PRECIOUS: %.depend %.cpp

include $(DEPS)
