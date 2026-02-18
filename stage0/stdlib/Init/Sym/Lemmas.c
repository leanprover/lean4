// Lean compiler output
// Module: Init.Sym.Lemmas
// Imports: public import Init.Data.Rat.Basic public import Init.Data.SInt.Basic public import Init.Data.Int.DivMod.Lemmas public import Init.Data.Nat.Dvd public import Init.Data.String.Basic import Init.Data.BitVec.Lemmas import Init.Data.Int.Order import Init.Data.UInt.Lemmas
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
lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
