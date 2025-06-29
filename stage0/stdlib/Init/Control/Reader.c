// Lean compiler output
// Module: Init.Control.Reader
// Imports: Init.Control.Basic Init.Control.Id Init.Control.Except
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
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure___redArg(lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_apply_2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_ReaderT_orElse___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_apply_3(x_5, lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_orElse___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_apply_1(x_5, x_7);
x_11 = lean_apply_3(x_8, lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_ReaderT_orElse___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_orElse___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_apply_1(x_2, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_ReaderT_failure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_ReaderT_failure(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_apply_2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_apply_1(x_3, x_5);
x_9 = lean_apply_3(x_6, lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
x_9 = lean_ctor_get(x_3, 1);
lean_dec(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_12, 0, x_8);
x_13 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_13, 0, x_7);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_14, 0, x_6);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_15, 0, x_5);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_2);
lean_ctor_set(x_3, 4, x_12);
lean_ctor_set(x_3, 3, x_13);
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
x_23 = lean_ctor_get(x_3, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instAlternativeOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_23);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_22);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_21);
lean_inc(x_20);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_29, 0, x_20);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, x_2);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set(x_33, 4, x_26);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_instAlternativeOfMonad___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_instAlternativeOfMonad___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_instAlternativeOfMonad___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_instAlternativeOfMonad___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lam__1), 3, 0);
x_4 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lam__2___boxed), 3, 0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instMonadControlReaderT___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instMonadControlReaderT___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_tryFinally(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
lean_object* initialize_Init_Control_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Id(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Except(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Reader(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
