// Lean compiler output
// Module: Init.Data.Int.Order
// Imports: Init.Data.Int.Lemmas Init.ByCases Init.RCases
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
LEAN_EXPORT lean_object* l_Int_instTransIntLeInstLEIntLtInstLTInt;
LEAN_EXPORT lean_object* l_Int_instTransIntLeInstLEInt;
LEAN_EXPORT lean_object* l_Int_instTransIntLtInstLTIntLeInstLEInt;
LEAN_EXPORT lean_object* l_Int_instTransIntLtInstLTInt;
static lean_object* _init_l_Int_instTransIntLeInstLEInt() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Int_instTransIntLtInstLTIntLeInstLEInt() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Int_instTransIntLeInstLEIntLtInstLTInt() {
_start:
{
return lean_box(0);
}
}
static lean_object* _init_l_Int_instTransIntLtInstLTInt() {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_ByCases(uint8_t builtin, lean_object*);
lean_object* initialize_Init_RCases(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Order(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_instTransIntLeInstLEInt = _init_l_Int_instTransIntLeInstLEInt();
l_Int_instTransIntLtInstLTIntLeInstLEInt = _init_l_Int_instTransIntLtInstLTIntLeInstLEInt();
l_Int_instTransIntLeInstLEIntLtInstLTInt = _init_l_Int_instTransIntLeInstLEIntLtInstLTInt();
l_Int_instTransIntLtInstLTInt = _init_l_Int_instTransIntLtInstLTInt();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
