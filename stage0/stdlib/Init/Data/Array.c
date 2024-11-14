// Lean compiler output
// Module: Init.Data.Array
// Imports: Init.Data.Array.Basic Init.Data.Array.QSort Init.Data.Array.BinSearch Init.Data.Array.InsertionSort Init.Data.Array.DecidableEq Init.Data.Array.Mem Init.Data.Array.Attach Init.Data.Array.BasicAux Init.Data.Array.Lemmas Init.Data.Array.TakeDrop Init.Data.Array.Bootstrap Init.Data.Array.GetLit Init.Data.Array.MapIdx Init.Data.Array.Set Init.Data.Array.Monadic
#include <lean/lean.h>
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
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_QSort(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_BinSearch(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_InsertionSort(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_BasicAux(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_TakeDrop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_QSort(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_BinSearch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_InsertionSort(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_TakeDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
