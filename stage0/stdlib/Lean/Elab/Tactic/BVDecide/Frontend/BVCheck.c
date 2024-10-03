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
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof___at_Lean_Elab_Tactic_BVDecide_Frontend_lratBitblaster___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3;
x_13 = 1;
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1;
x_15 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___spec__1(x_11, x_12, x_10, x_13, x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
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
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around.", 93, 93);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
x_28 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_18);
x_33 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8;
lean_inc(x_10);
lean_inc(x_9);
x_34 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_31, x_32, x_33, x_30, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
x_37 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_36, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
lean_inc(x_20);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_20);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
x_50 = l_Lean_Syntax_node1(x_20, x_49, x_48);
x_51 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_18);
x_56 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8;
lean_inc(x_10);
lean_inc(x_9);
x_57 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_54, x_55, x_56, x_53, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
x_60 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_59, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
lean_dec(x_15);
x_70 = lean_ctor_get(x_16, 0);
lean_inc(x_70);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_71 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(x_70, x_2, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = l_Lean_Elab_Tactic_replaceMainGoal(x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_74);
if (x_81 == 0)
{
return x_74;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_74, 0);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_74);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_85 = !lean_is_exclusive(x_71);
if (x_85 == 0)
{
return x_71;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_71, 0);
x_87 = lean_ctor_get(x_71, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_71);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_15);
if (x_89 == 0)
{
return x_15;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_15, 0);
x_91 = lean_ctor_get(x_15, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_15);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_12);
if (x_93 == 0)
{
return x_12;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_12, 0);
x_95 = lean_ctor_get(x_12, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_12);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
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
