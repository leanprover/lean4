// Lean compiler output
// Module: Init.Data.Default
// Imports: Init.Data.Basic Init.Data.Nat.Default Init.Data.Char.Default Init.Data.String.Default Init.Data.List.Default Init.Data.Int.Default Init.Data.Array.Default Init.Data.ByteArray.Default Init.Data.Fin.Default Init.Data.UInt Init.Data.RBTree.Default Init.Data.RBMap.Default Init.Data.Option.Default Init.Data.HashMap.Default Init.Data.Random Init.Data.Queue.Default
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
lean_object* initialize_Init_Data_Basic(lean_object*);
lean_object* initialize_Init_Data_Nat_Default(lean_object*);
lean_object* initialize_Init_Data_Char_Default(lean_object*);
lean_object* initialize_Init_Data_String_Default(lean_object*);
lean_object* initialize_Init_Data_List_Default(lean_object*);
lean_object* initialize_Init_Data_Int_Default(lean_object*);
lean_object* initialize_Init_Data_Array_Default(lean_object*);
lean_object* initialize_Init_Data_ByteArray_Default(lean_object*);
lean_object* initialize_Init_Data_Fin_Default(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_RBTree_Default(lean_object*);
lean_object* initialize_Init_Data_RBMap_Default(lean_object*);
lean_object* initialize_Init_Data_Option_Default(lean_object*);
lean_object* initialize_Init_Data_HashMap_Default(lean_object*);
lean_object* initialize_Init_Data_Random(lean_object*);
lean_object* initialize_Init_Data_Queue_Default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Nat_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Char_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_String_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_List_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Int_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Array_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_ByteArray_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Fin_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_UInt(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_RBTree_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_RBMap_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Option_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_HashMap_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Random(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Queue_Default(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
