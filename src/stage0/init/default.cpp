// Lean compiler output
// Module: init.default
// Imports: init.core init.control.default init.data.basic init.function init.coe init.wf init.data.default init.io init.util init.fix
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
void initialize_init_core();
void initialize_init_control_default();
void initialize_init_data_basic();
void initialize_init_function();
void initialize_init_coe();
void initialize_init_wf();
void initialize_init_data_default();
void initialize_init_io();
void initialize_init_util();
void initialize_init_fix();
static bool _G_initialized = false;
void initialize_init_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_core();
 initialize_init_control_default();
 initialize_init_data_basic();
 initialize_init_function();
 initialize_init_coe();
 initialize_init_wf();
 initialize_init_data_default();
 initialize_init_io();
 initialize_init_util();
 initialize_init_fix();
}
