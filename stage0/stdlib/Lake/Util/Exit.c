// Lean compiler output
// Module: Lake.Util.Exit
// Imports: Init.Data.UInt.Basic
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
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___rarg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___rarg(lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint32_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box_uint32(x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadExitOfMonadLift___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadExitOfMonadLift___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_6 = l_Lake_instMonadExitOfMonadLift___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___rarg(lean_object* x_1, lean_object* x_2, uint32_t x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; 
x_4 = 0;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box_uint32(x_3);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_exitIfErrorCode___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_exitIfErrorCode___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_5 = l_Lake_exitIfErrorCode___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Exit(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
