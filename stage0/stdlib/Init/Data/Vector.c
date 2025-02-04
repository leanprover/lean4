// Lean compiler output
// Module: Init.Data.Vector
// Imports: Init.Data.Vector.Basic Init.Data.Vector.Lemmas Init.Data.Vector.Lex Init.Data.Vector.MapIdx Init.Data.Vector.Count Init.Data.Vector.DecidableEq Init.Data.Vector.Zip Init.Data.Vector.OfFn Init.Data.Vector.Range Init.Data.Vector.Erase Init.Data.Vector.Monadic
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
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Lex(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_MapIdx(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Count(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_DecidableEq(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Zip(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_OfFn(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Erase(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Vector_Monadic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_MapIdx(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Count(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_DecidableEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Zip(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_OfFn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Erase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
