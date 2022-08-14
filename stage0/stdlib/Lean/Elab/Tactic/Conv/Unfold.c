// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Unfold
// Imports: Init Lean.Elab.Tactic.Unfold Lean.Elab.Tactic.Conv.Simp
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
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__16;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__10;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__7;
lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Tactic_elabSimpArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__6;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__3;
lean_object* l_Lean_Elab_Tactic_Conv_getLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__5;
lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__11;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__15;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__18;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__17;
lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at_Lean_Elab_Tactic_elabSimpArgs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Elab_Tactic_Conv_getLhs(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_unfold(x_16, x_13, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Tactic_Conv_applySimpResult(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___lambda__1), 11, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Tactic_withMainContext___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalUnfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Conv_evalUnfold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__4;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Conv", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unfold", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__8;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__12;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__13;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalUnfold", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalUnfold___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__17;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__16;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__18;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__1;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__2;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__4;
x_2 = lean_unsigned_to_nat(52u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__5;
x_4 = lean_unsigned_to_nat(62u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__16;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Unfold(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__7);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__8);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__9 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__9);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__10 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__10);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__11 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__11();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__11);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__12 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__12();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__12);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__13 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__13();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__13);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__14 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__14();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__14);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__15 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__15();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__15);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__16 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__16();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__16);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__17 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__17();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__17);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__18 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__18();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold___closed__18);
res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Tactic_Conv_evalUnfold_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
