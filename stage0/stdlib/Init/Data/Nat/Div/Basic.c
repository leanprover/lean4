// Lean compiler output
// Module: Init.Data.Nat.Div.Basic
// Imports: Init.WF Init.WFTactics Init.Data.Nat.Basic Init.MetaTypes
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
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div_inductionOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_instMod___closed__0;
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instMod;
LEAN_EXPORT lean_object* l_Nat_div_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_instDvd;
LEAN_EXPORT lean_object* l_Nat_instDiv;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Nat_instDiv___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_div_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div_exact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Nat_instDvd() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_div_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_le(x_1, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_sub(x_3, x_1);
x_9 = l_Nat_div_go___redArg(x_1, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_nat_add(x_9, x_6);
lean_dec(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Nat_div_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_div_go___redArg(x_1, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_div_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Nat_div_go___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_div_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_div_go(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_div(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_instDiv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instDiv() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instDiv___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_1(x_2, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Nat_Div_Basic_0__Nat_div_go_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_3(x_4, x_1, x_2, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_nat_sub(x_1, x_2);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Nat_div_inductionOn___redArg(x_10, x_2, x_3, x_4);
x_12 = lean_apply_4(x_3, x_1, x_2, lean_box(0), x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_div_inductionOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_div_inductionOn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_divExact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_div_exact(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_mod(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_instMod___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Nat_instMod() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instMod___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_1(x_3, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_2(x_4, x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Nat_Div_Basic_0__Nat_mod_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_div_inductionOn___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_mod_inductionOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_div_inductionOn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_WF(uint8_t builtin, lean_object*);
lean_object* initialize_Init_WFTactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_MetaTypes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_WF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_instDvd = _init_l_Nat_instDvd();
lean_mark_persistent(l_Nat_instDvd);
l_Nat_instDiv___closed__0 = _init_l_Nat_instDiv___closed__0();
lean_mark_persistent(l_Nat_instDiv___closed__0);
l_Nat_instDiv = _init_l_Nat_instDiv();
lean_mark_persistent(l_Nat_instDiv);
l_Nat_instMod___closed__0 = _init_l_Nat_instMod___closed__0();
lean_mark_persistent(l_Nat_instMod___closed__0);
l_Nat_instMod = _init_l_Nat_instMod();
lean_mark_persistent(l_Nat_instMod);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
