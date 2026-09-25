CXX ?= c++
AR ?= ar

OBJS = $(patsubst src/%.cpp,%.o,$(shell ls src/*.cpp | grep -v mobical))
# `cadical.cpp` provides the command line application's `main`
LIB_OBJS = $(filter-out cadical.o,$(OBJS))

.PHONY: all
all: ../../cadical$(CMAKE_EXECUTABLE_SUFFIX) ../../libcadical.a

%.o: src/%.cpp
	$(CXX) -std=c++11 -O3 -DNDEBUG -DNBUILD $(CXXFLAGS) -c $< -o $@

../../cadical$(CMAKE_EXECUTABLE_SUFFIX): $(OBJS)
	$(CXX) -o $@ $^ $(LDFLAGS)

../../libcadical.a: $(LIB_OBJS)
	rm -f $@
	$(AR) rcs $@ $^
