// Lean compiler output
// Module: Lake.Util.Error
// Imports: Init.System.IO
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
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO;
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorExceptString;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorExceptString___lam__0(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_EIO_toBaseIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadErrorOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_instMonadErrorOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_mk_io_user_error(x_2);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_instMonadErrorIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorIO___lam__0), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorEIOString___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instMonadErrorEIOString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorEIOString___lam__0), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorExceptString___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instMonadErrorExceptString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorExceptString___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_apply_2(x_3, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_Lake_MonadError_runEIO___redArg___lam__0), 4, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runEIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, lean_box(0));
lean_closure_set(x_12, 2, x_8);
x_13 = lean_apply_2(x_6, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_MonadError_runEIO___redArg___lam__0), 4, 3);
lean_closure_set(x_14, 0, x_7);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_11);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_io_error_to_string(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_2(x_3, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_MonadError_runIO___redArg___lam__0), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_MonadError_runIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, lean_box(0));
lean_closure_set(x_10, 2, x_6);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_MonadError_runIO___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_9);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Error(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadErrorIO = _init_l_Lake_instMonadErrorIO();
lean_mark_persistent(l_Lake_instMonadErrorIO);
l_Lake_instMonadErrorEIOString = _init_l_Lake_instMonadErrorEIOString();
lean_mark_persistent(l_Lake_instMonadErrorEIOString);
l_Lake_instMonadErrorExceptString = _init_l_Lake_instMonadErrorExceptString();
lean_mark_persistent(l_Lake_instMonadErrorExceptString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
