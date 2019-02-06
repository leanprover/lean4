// Lean compiler output
// Module: init.data.string.default
// Imports: init.data.string.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
void initialize_init_data_string_basic();
static bool _G_initialized = false;
void initialize_init_data_string_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_string_basic();
}
