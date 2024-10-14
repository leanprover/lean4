// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVCheck
// Imports: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide Lean.Meta.Tactic.TryThis Std.Tactic.BVDecide.Syntax
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__7;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__4;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7;
lean_object* l_Lean_TSyntax_getString(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2;
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6;
lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_MVarId_elabFalseOrByContra___spec__1___rarg(lean_object*);
lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___at_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logWarning___at_Lean_Widget_initFn____x40_Lean_Widget_UserWidget___hyg_240____spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__6;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__4;
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__5;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__8;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_14, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_22, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cannot compute parent directory of '", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_System_FilePath_parent(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_Lean_MessageData_ofFormat(x_10);
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_System_FilePath_join(x_10, x_1);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVDecide", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reflect", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("verifyBVExpr", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__1;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__4;
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat_of_verifyBVExpr_eq_true", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__1;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__4;
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__7;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(x_8, x_9, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__6;
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__8;
x_15 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___at_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___spec__8(x_11, x_1, x_2, x_13, x_14, x_3, x_4, x_5, x_6, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Preparing LRAT reflection term", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__3;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2), 7, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3;
x_14 = 1;
x_15 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1;
x_16 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___spec__1(x_12, x_13, x_11, x_14, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___boxed), 9, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvNormalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bv_normalize", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around.", 93, 93);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_15 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_9, 5);
lean_inc(x_18);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_18, x_19);
x_21 = lean_st_ref_get(x_10, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
lean_inc(x_20);
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 1, x_25);
lean_ctor_set(x_21, 0, x_20);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
x_27 = l_Lean_Syntax_node1(x_20, x_26, x_21);
x_28 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9;
lean_inc(x_9);
x_29 = l_Lean_logWarning___at_Lean_Widget_initFn____x40_Lean_Widget_UserWidget___hyg_240____spec__2(x_28, x_7, x_8, x_9, x_10, x_23);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 0, x_33);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_18);
x_37 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
lean_inc(x_10);
lean_inc(x_9);
x_38 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_35, x_36, x_37, x_34, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Elab_Tactic_replaceMainGoal(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_38);
if (x_52 == 0)
{
return x_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_38, 0);
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_27);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_60, 5, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_18);
x_62 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
lean_inc(x_10);
lean_inc(x_9);
x_63 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_60, x_61, x_62, x_59, x_7, x_8, x_9, x_10, x_56);
lean_dec(x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = l_Lean_Elab_Tactic_replaceMainGoal(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_75 = lean_ctor_get(x_63, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_77 = x_63;
} else {
 lean_dec_ref(x_63);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_79 = lean_ctor_get(x_21, 1);
lean_inc(x_79);
lean_dec(x_21);
x_80 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
lean_inc(x_20);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_20);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
x_83 = l_Lean_Syntax_node1(x_20, x_82, x_81);
x_84 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9;
lean_inc(x_9);
x_85 = l_Lean_logWarning___at_Lean_Widget_initFn____x40_Lean_Widget_UserWidget___hyg_240____spec__2(x_84, x_7, x_8, x_9, x_10, x_79);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_83);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_91, 3, x_90);
lean_ctor_set(x_91, 4, x_90);
lean_ctor_set(x_91, 5, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_18);
x_93 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
lean_inc(x_10);
lean_inc(x_9);
x_94 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_91, x_92, x_93, x_90, x_7, x_8, x_9, x_10, x_86);
lean_dec(x_92);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_box(0);
x_97 = l_Lean_Elab_Tactic_replaceMainGoal(x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_106 = lean_ctor_get(x_94, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_94, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_108 = x_94;
} else {
 lean_dec_ref(x_94);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_15, 1);
lean_inc(x_110);
lean_dec(x_15);
x_111 = lean_ctor_get(x_16, 0);
lean_inc(x_111);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_112 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(x_111, x_2, x_7, x_8, x_9, x_10, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_box(0);
x_115 = l_Lean_Elab_Tactic_replaceMainGoal(x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_113);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
x_118 = lean_box(0);
lean_ctor_set(x_115, 0, x_118);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_115);
if (x_122 == 0)
{
return x_115;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_115, 0);
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_115);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_126 = !lean_is_exclusive(x_112);
if (x_126 == 0)
{
return x_112;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_112, 0);
x_128 = lean_ctor_get(x_112, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_112);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_15);
if (x_130 == 0)
{
return x_15;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_15, 0);
x_132 = lean_ctor_get(x_15, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_15);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_12);
if (x_134 == 0)
{
return x_12;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_12, 0);
x_136 = lean_ctor_get(x_12, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_12);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvCheck", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_MVarId_elabFalseOrByContra___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4;
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_MVarId_elabFalseOrByContra___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_TSyntax_getString(x_17);
lean_dec(x_17);
lean_inc(x_4);
x_22 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___boxed), 11, 2);
lean_closure_set(x_25, 0, x_15);
lean_closure_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_Tactic_withMainContext___rarg(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Frontend", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVCheck", 7, 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalBvCheck", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2;
x_6 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3;
x_7 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4;
x_8 = l_Lean_Name_mkStr7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5;
x_5 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
