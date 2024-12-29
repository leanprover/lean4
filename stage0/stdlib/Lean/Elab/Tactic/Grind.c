// Lean compiler output
// Module: Lean.Elab.Tactic.Grind
// Imports: Init.Grind.Tactics Lean.Meta.Tactic.Grind Lean.Elab.Tactic.Basic
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
static lean_object* l_Lean_Elab_Tactic_grind___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__4;
lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_grind___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__9;
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__8;
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__5;
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__4;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyRfl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyRfl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_grind___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__2;
lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__10;
static lean_object* l_Lean_Elab_Tactic_grind___closed__3;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApplyRfl___closed__7;
static lean_object* _init_l_Lean_Elab_Tactic_grind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` failed\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_grind___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_grind___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_Grind_main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_List_isEmpty___rarg(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
x_13 = l_Lean_Elab_goalsToMessageData(x_10);
x_14 = l_Lean_Elab_Tactic_grind___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_grind___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_17, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(0);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_List_isEmpty___rarg(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Elab_goalsToMessageData(x_20);
x_24 = l_Lean_Elab_Tactic_grind___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_Tactic_grind___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_27, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyRfl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_grind(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalApplyRfl___closed__1;
x_2 = l_Lean_Elab_Tactic_evalApplyRfl___closed__2;
x_3 = l_Lean_Elab_Tactic_evalApplyRfl___closed__3;
x_4 = l_Lean_Elab_Tactic_evalApplyRfl___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `grind` tactic is experimental and still under development. Avoid using it in production projects", 101, 101);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalApplyRfl___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalApplyRfl___closed__7;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_grind", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalApplyRfl___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyRfl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalApplyRfl___closed__5;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_Elab_Tactic_evalApplyRfl___closed__8;
x_15 = 1;
lean_inc(x_8);
x_16 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_1, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Term_getDeclName_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Tactic_evalApplyRfl___closed__10;
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyRfl___lambda__1), 7, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = l_Lean_Elab_Tactic_withMainContext___rarg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyRfl___lambda__1), 7, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_Lean_Elab_Tactic_withMainContext___rarg(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalApplyRfl", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalApplyRfl___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalApplyRfl___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyRfl), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__4;
x_3 = l_Lean_Elab_Tactic_evalApplyRfl___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_grind___closed__1 = _init_l_Lean_Elab_Tactic_grind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_grind___closed__1);
l_Lean_Elab_Tactic_grind___closed__2 = _init_l_Lean_Elab_Tactic_grind___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_grind___closed__2);
l_Lean_Elab_Tactic_grind___closed__3 = _init_l_Lean_Elab_Tactic_grind___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_grind___closed__3);
l_Lean_Elab_Tactic_grind___closed__4 = _init_l_Lean_Elab_Tactic_grind___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_grind___closed__4);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalApplyRfl___spec__1___rarg___closed__2);
l_Lean_Elab_Tactic_evalApplyRfl___closed__1 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__1);
l_Lean_Elab_Tactic_evalApplyRfl___closed__2 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__2);
l_Lean_Elab_Tactic_evalApplyRfl___closed__3 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__3);
l_Lean_Elab_Tactic_evalApplyRfl___closed__4 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__4);
l_Lean_Elab_Tactic_evalApplyRfl___closed__5 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__5);
l_Lean_Elab_Tactic_evalApplyRfl___closed__6 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__6);
l_Lean_Elab_Tactic_evalApplyRfl___closed__7 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__7);
l_Lean_Elab_Tactic_evalApplyRfl___closed__8 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__8);
l_Lean_Elab_Tactic_evalApplyRfl___closed__9 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__9);
l_Lean_Elab_Tactic_evalApplyRfl___closed__10 = _init_l_Lean_Elab_Tactic_evalApplyRfl___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApplyRfl___closed__10);
l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalApplyRfl__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
