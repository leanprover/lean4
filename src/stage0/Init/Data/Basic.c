// Lean compiler output
// Module: Init.Data.Basic
// Imports: Init.Data.Nat.Basic Init.Data.Fin.Basic Init.Data.List.Basic Init.Data.Char.Basic Init.Data.String.Basic Init.Data.Option.Basic Init.Data.UInt Init.Data.Repr Init.Data.ToString
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
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
lean_object* initialize_Init_Data_Fin_Basic(lean_object*);
lean_object* initialize_Init_Data_List_Basic(lean_object*);
lean_object* initialize_Init_Data_Char_Basic(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Repr(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Basic(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Nat_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Fin_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_List_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Char_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_String_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Option_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_UInt(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Repr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_ToString(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
