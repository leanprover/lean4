// Lean compiler output
// Module: init.default
// Imports: init.core init.control.default init.data.basic init.version init.function init.coe init.wf init.data.default init.io
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
void _l_initialize__l_s4_init_s4_core();
void _l_initialize__l_s4_init_s7_control_s7_default();
void _l_initialize__l_s4_init_s4_data_s5_basic();
void _l_initialize__l_s4_init_s7_version();
void _l_initialize__l_s4_init_s8_function();
void _l_initialize__l_s4_init_s3_coe();
void _l_initialize__l_s4_init_s2_wf();
void _l_initialize__l_s4_init_s4_data_s7_default();
void _l_initialize__l_s4_init_s2_io();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_default() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_core();
 _l_initialize__l_s4_init_s7_control_s7_default();
 _l_initialize__l_s4_init_s4_data_s5_basic();
 _l_initialize__l_s4_init_s7_version();
 _l_initialize__l_s4_init_s8_function();
 _l_initialize__l_s4_init_s3_coe();
 _l_initialize__l_s4_init_s2_wf();
 _l_initialize__l_s4_init_s4_data_s7_default();
 _l_initialize__l_s4_init_s2_io();
}
