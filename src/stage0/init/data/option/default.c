// Lean compiler output
// Module: Init.Data.Option.Default
// Imports: Init.Data.Option.Basic Init.Data.Option.BasicAux Init.Data.Option.Instances
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
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
lean_object* initialize_Init_Data_Option_BasicAux(lean_object*);
lean_object* initialize_Init_Data_Option_Instances(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Option_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Option_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Option_BasicAux(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Option_Instances(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
