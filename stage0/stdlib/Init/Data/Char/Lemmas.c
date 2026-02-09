// Lean compiler output
// Module: Init.Data.Char.Lemmas
// Imports: import all Init.Data.Char.Basic public import Init.Data.Char.Basic public import Init.Ext import Init.Data.UInt.Lemmas
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
LEAN_EXPORT lean_object* l_Char_leTrans;
LEAN_EXPORT lean_object* l_Char_ltTrans;
LEAN_EXPORT lean_object* l_Char_notLTTrans;
static lean_object* _init_l_Char_leTrans() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Char_ltTrans() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Char_notLTTrans() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Char_leTrans = _init_l_Char_leTrans();
l_Char_ltTrans = _init_l_Char_ltTrans();
l_Char_notLTTrans = _init_l_Char_notLTTrans();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
