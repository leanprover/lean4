CXX ?= c++
AR ?= ar

OBJS = $(patsubst src/%.cpp,%.o,$(shell ls src/*.cpp | grep -v mobical))
# `cadical.cpp` provides the command line application's `main`
LIB_OBJS = $(filter-out cadical.o,$(OBJS))

.PHONY: all FORCE
all: ../../cadical$(CMAKE_EXECUTABLE_SUFFIX) ../../libcadical.a

# `libcadical.a` is linked into the Lean libraries, so objects left over from a different toolchain
# would be an ABI hazard; rewrite the stamp only when the flags actually change
.flags: FORCE
	@echo '$(CXX) $(CXXFLAGS)' | cmp -s - $@ || echo '$(CXX) $(CXXFLAGS)' > $@
FORCE:

%.o: src/%.cpp .flags
	$(CXX) -std=c++11 -O3 -DNDEBUG -DNBUILD $(CXXFLAGS) -c $< -o $@

../../cadical$(CMAKE_EXECUTABLE_SUFFIX): $(OBJS)
	$(CXX) -o $@ $^ $(LDFLAGS)

../../libcadical.a: $(LIB_OBJS)
	rm -f $@
	$(AR) rcs $@ $^
