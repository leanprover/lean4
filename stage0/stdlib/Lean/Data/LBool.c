// Lean compiler output
// Module: Lean.Data.LBool
// Imports: Init
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
lean_object* l_Lean_LBool_neg_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LBool_toString(uint8_t);
lean_object* l_toLBoolM___rarg___lambda__1(lean_object*, uint8_t);
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(uint8_t, uint8_t);
lean_object* l_Lean_LBool_instToStringLBool;
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1(lean_object*);
lean_object* l_Lean_LBool_toString___boxed(lean_object*);
extern lean_object* l_instReprBool___closed__2;
lean_object* l_Bool_toLBool_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_toLBoolM(lean_object*);
lean_object* l_Bool_toLBool_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LBool_neg_match__1(lean_object*);
lean_object* l_Lean_LBool_neg_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_22151____closed__8;
uint8_t l_Lean_LBool_and(uint8_t, uint8_t);
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LBool_and_match__1(lean_object*);
lean_object* l_Lean_LBool_neg___boxed(lean_object*);
lean_object* l_Bool_toLBool___boxed(lean_object*);
lean_object* l_Lean_LBool_and___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LBool_and_match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instInhabitedLBool;
lean_object* l_Lean_instBEqLBool___closed__1;
lean_object* l_toLBoolM___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instBEqLBool;
lean_object* l_Bool_toLBool_match__1(lean_object*);
uint8_t l_Lean_LBool_neg(uint8_t);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_LBool_toString___closed__1;
lean_object* l_Lean_LBool_and_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11____boxed(lean_object*, lean_object*);
lean_object* l_toLBoolM___rarg(lean_object*, lean_object*);
lean_object* l_Lean_LBool_instToStringLBool___closed__1;
static uint8_t _init_l_Lean_instInhabitedLBool() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_box(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_box(x_1);
x_11 = lean_box(x_2);
x_12 = lean_apply_2(x_6, x_10, x_11);
return x_12;
}
}
case 1:
{
lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_box(x_2);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_4, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_4);
x_16 = lean_box(x_1);
x_17 = lean_box(x_2);
x_18 = lean_apply_2(x_6, x_16, x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(x_2);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = lean_apply_1(x_5, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_5);
x_22 = lean_box(x_1);
x_23 = lean_box(x_2);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
}
}
}
}
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11__match__1___rarg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
}
}
}
lean_object* l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqLBool___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_11____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqLBool() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqLBool___closed__1;
return x_1;
}
}
lean_object* l_Lean_LBool_neg_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_LBool_neg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LBool_neg_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LBool_neg_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_LBool_neg_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
uint8_t l_Lean_LBool_neg(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 2;
return x_4;
}
}
}
}
lean_object* l_Lean_LBool_neg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_LBool_neg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_LBool_and_match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_box(x_2);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_box(x_1);
x_9 = lean_box(x_2);
x_10 = lean_apply_2(x_4, x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_LBool_and_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_LBool_and_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LBool_and_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_LBool_and_match__1___rarg(x_5, x_6, x_3, x_4);
return x_7;
}
}
uint8_t l_Lean_LBool_and(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(x_1);
if (lean_obj_tag(x_3) == 1)
{
return x_2;
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
lean_object* l_Lean_LBool_and___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_LBool_and(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_LBool_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("undef");
return x_1;
}
}
lean_object* l_Lean_LBool_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_22151____closed__8;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_instReprBool___closed__2;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_LBool_toString___closed__1;
return x_4;
}
}
}
}
lean_object* l_Lean_LBool_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_LBool_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_LBool_instToStringLBool___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LBool_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_LBool_instToStringLBool() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LBool_instToStringLBool___closed__1;
return x_1;
}
}
lean_object* l_Bool_toLBool_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Bool_toLBool_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Bool_toLBool_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Bool_toLBool_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Bool_toLBool_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Bool_toLBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Bool_toLBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Bool_toLBool(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_toLBoolM___rarg___lambda__1(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Bool_toLBool(x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_toLBoolM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_toLBoolM___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_2, x_4);
return x_5;
}
}
lean_object* l_toLBoolM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_toLBoolM___rarg), 2, 0);
return x_2;
}
}
lean_object* l_toLBoolM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_toLBoolM___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_LBool(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLBool = _init_l_Lean_instInhabitedLBool();
l_Lean_instBEqLBool___closed__1 = _init_l_Lean_instBEqLBool___closed__1();
lean_mark_persistent(l_Lean_instBEqLBool___closed__1);
l_Lean_instBEqLBool = _init_l_Lean_instBEqLBool();
lean_mark_persistent(l_Lean_instBEqLBool);
l_Lean_LBool_toString___closed__1 = _init_l_Lean_LBool_toString___closed__1();
lean_mark_persistent(l_Lean_LBool_toString___closed__1);
l_Lean_LBool_instToStringLBool___closed__1 = _init_l_Lean_LBool_instToStringLBool___closed__1();
lean_mark_persistent(l_Lean_LBool_instToStringLBool___closed__1);
l_Lean_LBool_instToStringLBool = _init_l_Lean_LBool_instToStringLBool();
lean_mark_persistent(l_Lean_LBool_instToStringLBool);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
