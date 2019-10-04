// Lean compiler output
// Module: Init.Data.Array.Default
// Imports: Init.Data.Array.Basic Init.Data.Array.QSort Init.Data.Array.BinSearch
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
lean_object* initialize_Init_Data_Array_Basic(lean_object*);
lean_object* initialize_Init_Data_Array_QSort(lean_object*);
lean_object* initialize_Init_Data_Array_BinSearch(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Array_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Array_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Array_QSort(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Array_BinSearch(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
