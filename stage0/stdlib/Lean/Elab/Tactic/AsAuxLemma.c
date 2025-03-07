// Lean compiler output
// Module: Lean.Elab.Tactic.AsAuxLemma
// Imports: Init.Tactics Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Meta Lean.MetavarContext Lean.Meta.Closure
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__3___closed__3;
static lean_object* l_elabAsAuxLemma___lambda__3___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__2___closed__3;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_elabAsAuxLemma___closed__1;
static lean_object* l___regBuiltin_elabAsAuxLemma__1___closed__3;
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__2___closed__1;
static lean_object* l_elabAsAuxLemma___closed__2;
static lean_object* l_elabAsAuxLemma___lambda__3___closed__8;
static lean_object* l_elabAsAuxLemma___closed__3;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__3___closed__7;
static lean_object* l_elabAsAuxLemma___closed__4;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_elabAsAuxLemma__1___closed__4;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_elabAsAuxLemma__1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__2___closed__2;
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__2___closed__4;
static lean_object* l_elabAsAuxLemma___lambda__3___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_elabAsAuxLemma__1(lean_object*);
static lean_object* l_elabAsAuxLemma___closed__5;
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_elabAsAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__3___closed__5;
static lean_object* l_elabAsAuxLemma___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_elabAsAuxLemma___lambda__3___closed__4;
static lean_object* l_elabAsAuxLemma___lambda__3___closed__2;
static lean_object* l_elabAsAuxLemma___lambda__2___closed__5;
LEAN_EXPORT uint8_t l_elabAsAuxLemma___lambda__1(lean_object*);
static lean_object* l___regBuiltin_elabAsAuxLemma__1___closed__2;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_elabAsAuxLemma___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("auxLemma", 8, 8);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_elabAsAuxLemma___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("AsAuxLemma", 10, 10);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_elabAsAuxLemma___lambda__2___closed__3;
x_2 = l_elabAsAuxLemma___lambda__2___closed__4;
x_3 = l_elabAsAuxLemma___lambda__2___closed__5;
x_4 = l_elabAsAuxLemma___lambda__2___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_9 = l_Lean_Expr_mvar___override(x_1);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_elabAsAuxLemma___lambda__2___closed__2;
x_14 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_13, x_6, x_7, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_elabAsAuxLemma___lambda__2___closed__7;
x_21 = l_Lean_Name_append(x_20, x_15);
x_22 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_mkAuxTheorem(x_21, x_18, x_11, x_22, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_24, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_2);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabAsAuxLemma___lambda__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_elabAsAuxLemma___lambda__3___closed__2;
x_3 = l_elabAsAuxLemma___lambda__3___closed__1;
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
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_elabAsAuxLemma___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = 1;
x_5 = 0;
x_6 = l_elabAsAuxLemma___lambda__3___closed__3;
x_7 = l_elabAsAuxLemma___lambda__3___closed__4;
x_8 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 4, x_3);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 3, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 4, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 5, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 6, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 7, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 8, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 10, x_4);
return x_8;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_1);
return x_3;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot abstract term into auxiliary lemma because there are open goals.", 71, 71);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabAsAuxLemma___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_elabAsAuxLemma___lambda__3___closed__5;
x_16 = l_elabAsAuxLemma___lambda__3___closed__6;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_17 = l_Lean_Elab_runTactic(x_12, x_1, x_15, x_16, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_List_isEmpty___rarg(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_12);
x_22 = l_elabAsAuxLemma___lambda__3___closed__8;
x_23 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_22, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_elabAsAuxLemma___lambda__2(x_12, x_14, x_28, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Tactic_replaceMainGoal(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_28);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_29);
if (x_41 == 0)
{
return x_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_29, 0);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_29);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
return x_11;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_elabAsAuxLemma___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("as_aux_lemma", 12, 12);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_elabAsAuxLemma___lambda__2___closed__3;
x_2 = l_elabAsAuxLemma___closed__1;
x_3 = l_elabAsAuxLemma___lambda__2___closed__5;
x_4 = l_elabAsAuxLemma___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_elabAsAuxLemma___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid as_aux_lemma syntax", 27, 27);
return x_1;
}
}
static lean_object* _init_l_elabAsAuxLemma___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_elabAsAuxLemma___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_elabAsAuxLemma___closed__3;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_elabAsAuxLemma___closed__5;
x_14 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = lean_alloc_closure((void*)(l_elabAsAuxLemma___lambda__3___boxed), 10, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_elabAsAuxLemma___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_elabAsAuxLemma___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_elabAsAuxLemma___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_elabAsAuxLemma___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_elabAsAuxLemma__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabAsAuxLemma", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_elabAsAuxLemma__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_elabAsAuxLemma__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_elabAsAuxLemma__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_elabAsAuxLemma__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_elabAsAuxLemma), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_elabAsAuxLemma__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_elabAsAuxLemma__1___closed__3;
x_3 = l_elabAsAuxLemma___closed__3;
x_4 = l___regBuiltin_elabAsAuxLemma__1___closed__2;
x_5 = l___regBuiltin_elabAsAuxLemma__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_elabAsAuxLemma___lambda__2___closed__1 = _init_l_elabAsAuxLemma___lambda__2___closed__1();
lean_mark_persistent(l_elabAsAuxLemma___lambda__2___closed__1);
l_elabAsAuxLemma___lambda__2___closed__2 = _init_l_elabAsAuxLemma___lambda__2___closed__2();
lean_mark_persistent(l_elabAsAuxLemma___lambda__2___closed__2);
l_elabAsAuxLemma___lambda__2___closed__3 = _init_l_elabAsAuxLemma___lambda__2___closed__3();
lean_mark_persistent(l_elabAsAuxLemma___lambda__2___closed__3);
l_elabAsAuxLemma___lambda__2___closed__4 = _init_l_elabAsAuxLemma___lambda__2___closed__4();
lean_mark_persistent(l_elabAsAuxLemma___lambda__2___closed__4);
l_elabAsAuxLemma___lambda__2___closed__5 = _init_l_elabAsAuxLemma___lambda__2___closed__5();
lean_mark_persistent(l_elabAsAuxLemma___lambda__2___closed__5);
l_elabAsAuxLemma___lambda__2___closed__6 = _init_l_elabAsAuxLemma___lambda__2___closed__6();
lean_mark_persistent(l_elabAsAuxLemma___lambda__2___closed__6);
l_elabAsAuxLemma___lambda__2___closed__7 = _init_l_elabAsAuxLemma___lambda__2___closed__7();
lean_mark_persistent(l_elabAsAuxLemma___lambda__2___closed__7);
l_elabAsAuxLemma___lambda__3___closed__1 = _init_l_elabAsAuxLemma___lambda__3___closed__1();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__1);
l_elabAsAuxLemma___lambda__3___closed__2 = _init_l_elabAsAuxLemma___lambda__3___closed__2();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__2);
l_elabAsAuxLemma___lambda__3___closed__3 = _init_l_elabAsAuxLemma___lambda__3___closed__3();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__3);
l_elabAsAuxLemma___lambda__3___closed__4 = _init_l_elabAsAuxLemma___lambda__3___closed__4();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__4);
l_elabAsAuxLemma___lambda__3___closed__5 = _init_l_elabAsAuxLemma___lambda__3___closed__5();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__5);
l_elabAsAuxLemma___lambda__3___closed__6 = _init_l_elabAsAuxLemma___lambda__3___closed__6();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__6);
l_elabAsAuxLemma___lambda__3___closed__7 = _init_l_elabAsAuxLemma___lambda__3___closed__7();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__7);
l_elabAsAuxLemma___lambda__3___closed__8 = _init_l_elabAsAuxLemma___lambda__3___closed__8();
lean_mark_persistent(l_elabAsAuxLemma___lambda__3___closed__8);
l_elabAsAuxLemma___closed__1 = _init_l_elabAsAuxLemma___closed__1();
lean_mark_persistent(l_elabAsAuxLemma___closed__1);
l_elabAsAuxLemma___closed__2 = _init_l_elabAsAuxLemma___closed__2();
lean_mark_persistent(l_elabAsAuxLemma___closed__2);
l_elabAsAuxLemma___closed__3 = _init_l_elabAsAuxLemma___closed__3();
lean_mark_persistent(l_elabAsAuxLemma___closed__3);
l_elabAsAuxLemma___closed__4 = _init_l_elabAsAuxLemma___closed__4();
lean_mark_persistent(l_elabAsAuxLemma___closed__4);
l_elabAsAuxLemma___closed__5 = _init_l_elabAsAuxLemma___closed__5();
lean_mark_persistent(l_elabAsAuxLemma___closed__5);
l___regBuiltin_elabAsAuxLemma__1___closed__1 = _init_l___regBuiltin_elabAsAuxLemma__1___closed__1();
lean_mark_persistent(l___regBuiltin_elabAsAuxLemma__1___closed__1);
l___regBuiltin_elabAsAuxLemma__1___closed__2 = _init_l___regBuiltin_elabAsAuxLemma__1___closed__2();
lean_mark_persistent(l___regBuiltin_elabAsAuxLemma__1___closed__2);
l___regBuiltin_elabAsAuxLemma__1___closed__3 = _init_l___regBuiltin_elabAsAuxLemma__1___closed__3();
lean_mark_persistent(l___regBuiltin_elabAsAuxLemma__1___closed__3);
l___regBuiltin_elabAsAuxLemma__1___closed__4 = _init_l___regBuiltin_elabAsAuxLemma__1___closed__4();
lean_mark_persistent(l___regBuiltin_elabAsAuxLemma__1___closed__4);
if (builtin) {res = l___regBuiltin_elabAsAuxLemma__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
