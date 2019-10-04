// Lean compiler output
// Module: Init.Default
// Imports: Init.Core Init.Control.Default Init.Data.Basic Init.Coe Init.Wf Init.Data.Default Init.System.Default Init.Util Init.Fix
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init_Core(lean_object*);
lean_object* initialize_Init_Control_Default(lean_object*);
lean_object* initialize_Init_Data_Basic(lean_object*);
lean_object* initialize_Init_Coe(lean_object*);
lean_object* initialize_Init_Wf(lean_object*);
lean_object* initialize_Init_Data_Default(lean_object*);
lean_object* initialize_Init_System_Default(lean_object*);
lean_object* initialize_Init_Util(lean_object*);
lean_object* initialize_Init_Fix(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Core(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Coe(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Wf(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_System_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Util(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Fix(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
