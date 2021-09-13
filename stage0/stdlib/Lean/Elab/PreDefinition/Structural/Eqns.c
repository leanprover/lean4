// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Eqns
// Imports: Init Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural.Basic
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
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkEqns___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__10;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__1;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__8;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__4;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__9;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__7;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__3;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__5;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__12;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__6;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__13;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__2;
static lean_object* l_Lean_Elab_Structural_mkEqns___closed__11;
lean_object* l_Lean_Elab_Structural_mkEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_80_(lean_object*);
lean_object* l_Lean_Elab_Structural_mkEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Structural_mkEqns___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Structural_mkEqns___closed__2;
x_2 = l_Lean_Elab_Structural_mkEqns___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Structural_mkEqns___closed__4;
x_2 = l_Lean_Elab_Structural_mkEqns___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eqns");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Structural_mkEqns___closed__6;
x_2 = l_Lean_Elab_Structural_mkEqns___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkEqns___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkEqns:\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_mkEqns___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkEqns___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_mkEqns___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Structural_mkEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_9 = l_Lean_Elab_Structural_mkEqns___closed__8;
x_26 = lean_st_ref_get(x_7, x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = 0;
x_10 = x_31;
x_11 = x_30;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unbox(x_34);
lean_dec(x_34);
x_10 = x_36;
x_11 = x_35;
goto block_25;
}
block_25:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Structural_mkEqns___closed__9;
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_apply_8(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Structural_mkEqns___closed__11;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Structural_mkEqns___closed__13;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_9, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_8(x_12, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Structural_mkEqns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Structural_mkEqns___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Structural_mkEqns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Structural_mkEqns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_80_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Structural_mkEqns___closed__8;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Eqns(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_mkEqns___closed__1 = _init_l_Lean_Elab_Structural_mkEqns___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__1);
l_Lean_Elab_Structural_mkEqns___closed__2 = _init_l_Lean_Elab_Structural_mkEqns___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__2);
l_Lean_Elab_Structural_mkEqns___closed__3 = _init_l_Lean_Elab_Structural_mkEqns___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__3);
l_Lean_Elab_Structural_mkEqns___closed__4 = _init_l_Lean_Elab_Structural_mkEqns___closed__4();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__4);
l_Lean_Elab_Structural_mkEqns___closed__5 = _init_l_Lean_Elab_Structural_mkEqns___closed__5();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__5);
l_Lean_Elab_Structural_mkEqns___closed__6 = _init_l_Lean_Elab_Structural_mkEqns___closed__6();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__6);
l_Lean_Elab_Structural_mkEqns___closed__7 = _init_l_Lean_Elab_Structural_mkEqns___closed__7();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__7);
l_Lean_Elab_Structural_mkEqns___closed__8 = _init_l_Lean_Elab_Structural_mkEqns___closed__8();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__8);
l_Lean_Elab_Structural_mkEqns___closed__9 = _init_l_Lean_Elab_Structural_mkEqns___closed__9();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__9);
l_Lean_Elab_Structural_mkEqns___closed__10 = _init_l_Lean_Elab_Structural_mkEqns___closed__10();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__10);
l_Lean_Elab_Structural_mkEqns___closed__11 = _init_l_Lean_Elab_Structural_mkEqns___closed__11();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__11);
l_Lean_Elab_Structural_mkEqns___closed__12 = _init_l_Lean_Elab_Structural_mkEqns___closed__12();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__12);
l_Lean_Elab_Structural_mkEqns___closed__13 = _init_l_Lean_Elab_Structural_mkEqns___closed__13();
lean_mark_persistent(l_Lean_Elab_Structural_mkEqns___closed__13);
res = l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_80_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
