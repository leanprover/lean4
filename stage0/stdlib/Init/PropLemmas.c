// Lean compiler output
// Module: Init.PropLemmas
// Imports: Init.Core Init.NotationExtra
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
LEAN_EXPORT uint8_t l_decidable__of__iff___redArg(uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__iff___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_exists__prop__decidable___redArg(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__iff(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_forall__prop__decidable___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_forall__prop__decidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_exists__prop__decidable___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_decidable__of__bool___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_forall__prop__decidable(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_forall__prop__decidable___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidablePredComp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidablePredComp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_decidable__of__iff___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__iff_x27___redArg(uint8_t);
LEAN_EXPORT lean_object* l_decidable__of__bool___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Decidable_predToBool___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__bool(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_exists__prop__decidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__iff_x27(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidablePredComp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Decidable_predToBool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidablePredComp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_exists__prop__decidable(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_decidable__of__bool___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Or_by__cases___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Or_by__cases___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_1(x_2, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Or_by__cases(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Or_by__cases___redArg(x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Or_by__cases___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Or_by__cases(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_apply_1(x_2, lean_box(0));
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Or_by__cases_x27___redArg(x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Or_by__cases_x27___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Or_by__cases_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Or_by__cases_x27(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l_exists__prop__decidable___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_2, lean_box(0));
x_4 = lean_unbox(x_3);
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_exists__prop__decidable(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_exists__prop__decidable___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_exists__prop__decidable___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_exists__prop__decidable___redArg(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_exists__prop__decidable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_exists__prop__decidable(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_forall__prop__decidable___redArg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_1(x_2, lean_box(0));
x_6 = lean_unbox(x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_forall__prop__decidable(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_forall__prop__decidable___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_forall__prop__decidable___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_forall__prop__decidable___redArg(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_forall__prop__decidable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_forall__prop__decidable(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff___redArg(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
return x_4;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_decidable__of__iff___redArg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_decidable__of__iff(x_1, x_2, x_3, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff_x27___redArg(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_decidable__of__iff_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
return x_4;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_decidable__of__iff_x27___redArg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_decidable__of__iff_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_decidable__of__iff_x27(x_1, x_2, x_3, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Decidable_predToBool___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Decidable_predToBool___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Decidable_predToBool___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Decidable_predToBool___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Decidable_predToBool___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_instDecidablePredComp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidablePredComp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_instDecidablePredComp___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_instDecidablePredComp___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_instDecidablePredComp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_instDecidablePredComp(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_decidable__of__bool___redArg(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT uint8_t l_decidable__of__bool(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_decidable__of__bool___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_decidable__of__bool___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_decidable__of__bool___redArg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_decidable__of__bool___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_decidable__of__bool(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_PropLemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
