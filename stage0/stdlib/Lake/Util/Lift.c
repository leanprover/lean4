// Lean compiler output
// Module: Lake.Util.Lift
// Imports: Init.System.IO Init.Control.Option
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
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(lean_object*, lean_object*);
lean_object* l_EIO_toBaseIO(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_5, lean_box(0), x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1), 4, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instMonadLiftTOfMonadLift__lake___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadLiftTIdOfPure__lake___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_1, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0), 4, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_6, lean_box(0), x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg___lam__1), 5, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_instMonadLiftTReaderTOfBindOfMonadReaderOf__lake___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_1(x_7, x_6);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_3);
x_8 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2), 5, 4);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_5);
x_8 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3), 6, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_5);
lean_closure_set(x_8, 3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, lean_box(0));
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0), 5, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, lean_box(0));
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0), 4, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0), 5, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_EIO_toBaseIO), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, lean_box(0));
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0), 4, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0), 5, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_Option(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
