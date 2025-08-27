// Lean compiler output
// Module: Init.Data.Rat.Lemmas
// Imports: Init.Data.Rat.Basic Init.Data.Int.Bitwise.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0;
x_6 = lean_int_dec_lt(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_nat_abs(x_2);
x_8 = lean_apply_2(x_3, x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_9 = lean_nat_abs(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = lean_apply_2(x_4, x_1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_4(x_2, x_3, x_4, lean_box(0), lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Rat_numDenCasesOn___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, x_2, x_3, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Rat_numDenCasesOn_x27___redArg___lam__0), 5, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Rat_numDenCasesOn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Rat_numDenCasesOn_x27___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, x_2, x_3, lean_box(0), lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Rat_numDenCasesOn_x27_x27___redArg___lam__0), 5, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Rat_numDenCasesOn___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Rat_numDenCasesOn_x27_x27___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Rat_Lemmas(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Rat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0 = _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0();
lean_mark_persistent(l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
