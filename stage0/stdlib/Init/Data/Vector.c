// Lean compiler output
// Module: Init.Data.Vector
// Imports: public import Init.Data.Vector.Basic public import Init.Data.Vector.Lemmas public import Init.Data.Vector.Lex public import Init.Data.Vector.MapIdx public import Init.Data.Vector.Count public import Init.Data.Vector.DecidableEq public import Init.Data.Vector.Zip public import Init.Data.Vector.OfFn public import Init.Data.Vector.Range public import Init.Data.Vector.Erase public import Init.Data.Vector.Monadic public import Init.Data.Vector.InsertIdx public import Init.Data.Vector.FinRange public import Init.Data.Vector.Extract public import Init.Data.Vector.Perm public import Init.Data.Vector.Find public import Init.Data.Vector.Algebra public import Init.Data.Vector.Stream public import Init.Data.Vector.Nat public import Init.Data.Vector.Int
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
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lex(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_OfFn(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Range(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_FinRange(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Extract(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Perm(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Find(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Algebra(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Stream(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Int(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_FinRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Algebra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
