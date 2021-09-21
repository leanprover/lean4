// Lean compiler output
// Module: Lean.Elab.Tactic.Meta
// Imports: Init Lean.Elab.SyntheticMVars Lean.Elab.Tactic.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__6;
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__8;
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__7;
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__2;
lean_object* l_Lean_MetavarContext_instantiateMVarDeclMVars(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__2;
x_2 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__5;
x_3 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__4;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<runTactic>");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__7;
x_5 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__3;
x_6 = l_Lean_firstFrontendMacroScope;
x_7 = 1;
x_8 = 0;
x_9 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__6;
x_10 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_2);
lean_ctor_set(x_10, 4, x_6);
lean_ctor_set(x_10, 5, x_9);
lean_ctor_set(x_10, 6, x_3);
lean_ctor_set(x_10, 7, x_3);
lean_ctor_set_uint8(x_10, sizeof(void*)*8, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 2, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 3, x_7);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_evalTacticAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_1);
x_17 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_16, x_1);
lean_ctor_set(x_13, 0, x_17);
x_18 = lean_st_ref_set(x_6, x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lambda__1), 10, 1);
lean_closure_set(x_20, 0, x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run), 9, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_20);
x_22 = 0;
x_23 = 1;
x_24 = lean_box(x_22);
x_25 = lean_box(x_23);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed), 10, 3);
lean_closure_set(x_26, 0, x_21);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_Elab_Term_TermElabM_run___rarg(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
x_30 = lean_ctor_get(x_13, 2);
x_31 = lean_ctor_get(x_13, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
lean_inc(x_1);
x_32 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_28, x_1);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
x_34 = lean_st_ref_set(x_6, x_33, x_14);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_runTactic___lambda__1), 10, 1);
lean_closure_set(x_36, 0, x_2);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run), 9, 2);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
x_38 = 0;
x_39 = 1;
x_40 = lean_box(x_38);
x_41 = lean_box(x_39);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed), 10, 3);
lean_closure_set(x_42, 0, x_37);
lean_closure_set(x_42, 1, x_40);
lean_closure_set(x_42, 2, x_41);
x_43 = l_Lean_Elab_Term_TermElabM_run___rarg(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_43;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Meta(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__1 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__1);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__2 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__2);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__3 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__3);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__4 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__4);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__5 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__5);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__6 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__6);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__7 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__7);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__8 = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext___closed__8);
l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext = _init_l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Meta_0__Lean_Elab_runTactic_defaultContext);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
