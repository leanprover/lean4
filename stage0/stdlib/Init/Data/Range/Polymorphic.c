// Lean compiler output
// Module: Init.Data.Range.Polymorphic
// Imports: public import Init.Data.Range.Polymorphic.Basic public import Init.Data.Range.Polymorphic.Iterators public import Init.Data.Range.Polymorphic.Stream public import Init.Data.Range.Polymorphic.Lemmas public import Init.Data.Range.Polymorphic.Map public import Init.Data.Range.Polymorphic.Fin public import Init.Data.Range.Polymorphic.Char public import Init.Data.Range.Polymorphic.Nat public import Init.Data.Range.Polymorphic.Int public import Init.Data.Range.Polymorphic.BitVec public import Init.Data.Range.Polymorphic.UInt public import Init.Data.Range.Polymorphic.SInt public import Init.Data.Range.Polymorphic.NatLemmas public import Init.Data.Range.Polymorphic.IntLemmas public import Init.Data.Range.Polymorphic.GetElemTactic
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
lean_object* initialize_Init_Data_Range_Polymorphic_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Stream(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Map(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Char(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Int(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_SInt(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_NatLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_IntLemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_GetElemTactic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Map(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Char(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_NatLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_IntLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_GetElemTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
