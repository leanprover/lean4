// Lean compiler output
// Module: Init.Data.Range.Polymorphic
// Imports: Init.Data.Range.Polymorphic.Basic Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Stream Init.Data.Range.Polymorphic.Lemmas Init.Data.Range.Polymorphic.Nat Init.Data.Range.Polymorphic.Int Init.Data.Range.Polymorphic.BitVec Init.Data.Range.Polymorphic.UInt Init.Data.Range.Polymorphic.NatLemmas Init.Data.Range.Polymorphic.GetElemTactic
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
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_UInt(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_NatLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Stream(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_UInt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
