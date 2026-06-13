#include <cstdlib>

#include <lean/lean.h>

extern "C" void * mi_malloc_small(size_t size) noexcept {
    return std::malloc(size);
}

extern "C" lean_object * lean_io_eprintln(...) {
    return lean_box(0);
}

extern "C" lean_object * lean_stream_of_handle(...) {
    return lean_box(0);
}
