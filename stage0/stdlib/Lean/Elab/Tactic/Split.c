// Lean compiler output
// Module: Lean.Elab.Tactic.Split
// Imports: Init Lean.Meta.Tactic.Split Lean.Elab.Tactic.Basic
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSplit(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__12;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__3;
lean_object* l_Lean_Elab_Tactic_evalSplit___boxed(lean_object*);
lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSplit_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__14;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__13;
lean_object* l_Lean_Elab_Tactic_evalSplit_match__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSplit___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__11;
lean_object* l_Lean_throwError___at_Lean_Meta_Split_splitMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSplit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__9;
lean_object* l_Lean_Elab_Tactic_evalSplit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'split' tactic failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__2;
x_17 = l_Lean_throwError___at_Lean_Meta_Split_splitMatch___spec__1(x_16, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Elab_Tactic_replaceMainGoal(x_23, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSplit___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1), 9, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_evalSplit___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalSplit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalSplit(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__4;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("split");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalSplit");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSplit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__8;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__13;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__14;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Split(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSplit___rarg___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalSplit___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalSplit___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSplit___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__7);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__8);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__9 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__9);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__10 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__10);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__11 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__11();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__11);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__12 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__12();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__12);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__13 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__13();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__13);
l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__14 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__14();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSplit___closed__14);
res = l___regBuiltin_Lean_Elab_Tactic_evalSplit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
