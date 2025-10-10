// Lean compiler output
// Module: Init.Data.Array
// Imports: public import Init.Data.Array.Basic public import Init.Data.Array.QSort public import Init.Data.Array.BinSearch public import Init.Data.Array.InsertionSort public import Init.Data.Array.DecidableEq public import Init.Data.Array.Mem public import Init.Data.Array.Attach public import Init.Data.Array.BasicAux public import Init.Data.Array.Lemmas public import Init.Data.Array.TakeDrop public import Init.Data.Array.Bootstrap public import Init.Data.Array.GetLit public import Init.Data.Array.MapIdx public import Init.Data.Array.Set public import Init.Data.Array.Monadic public import Init.Data.Array.FinRange public import Init.Data.Array.Perm public import Init.Data.Array.Find public import Init.Data.Array.Lex public import Init.Data.Array.Range public import Init.Data.Array.Erase public import Init.Data.Array.Zip public import Init.Data.Array.InsertIdx public import Init.Data.Array.Extract
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
lean_object* initialize_Init_Data_Array_FinRange(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Perm(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Find(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Lex(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Erase(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Zip(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_InsertIdx(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Extract(uint8_t builtin, lean_object*);
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
res = initialize_Init_Data_Array_FinRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Perm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Find(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Erase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Zip(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_InsertIdx(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Extract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
