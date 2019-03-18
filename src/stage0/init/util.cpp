// Lean compiler output
// Module: init.util
// Imports: init.data.string.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_dbg__sleep___boxed(obj*, obj*, obj*);
obj* l_dbg__trace___boxed(obj*, obj*, obj*);
obj* l_dbg__trace___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::dbg_trace(x_1, x_2);
return x_3;
}
}
obj* l_dbg__sleep___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = lean::dbg_sleep(x_3, x_2);
return x_4;
}
}
obj* initialize_init_data_string_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_util(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
w = initialize_init_data_string_basic(w);
return w;
}
