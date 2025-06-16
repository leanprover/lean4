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
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__4;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1;
lean_object* l_Lean_TSyntax_getString(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at_Lean_Meta_reportDiag___spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__5;
lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__3;
lean_object* l_Lean_withTraceNode___at_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2;
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__5;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_closeWithBVReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_System_FilePath_join(x_11, x_1);
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_TacticContext_new(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_lratChecker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile(x_8, x_10, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_toReflectionProof(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__5() {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__4;
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__5;
x_13 = 1;
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__2___closed__1;
x_15 = l_Lean_withTraceNode___at_Lean_Elab_Tactic_BVDecide_Frontend_bvUnsat___spec__1(x_11, x_12, x_10, x_13, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
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
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_bvNormalize(x_15, x_1, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_4);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_11, 5);
lean_inc(x_20);
x_21 = 0;
x_22 = l_Lean_SourceInfo_fromRef(x_20, x_21);
x_23 = lean_st_ref_get(x_12, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
lean_inc(x_22);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_27);
lean_ctor_set(x_23, 0, x_22);
x_28 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
x_29 = l_Lean_Syntax_node2(x_22, x_28, x_23, x_2);
x_30 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9;
x_31 = 1;
lean_inc(x_11);
x_32 = l_Lean_log___at_Lean_Meta_reportDiag___spec__1(x_30, x_31, x_21, x_9, x_10, x_11, x_12, x_25);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 0, x_36);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_20);
x_40 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
lean_inc(x_12);
lean_inc(x_11);
x_41 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_38, x_39, x_40, x_37, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Tactic_replaceMainGoal(x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
return x_41;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_32, 1);
lean_inc(x_59);
lean_dec(x_32);
x_60 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_29);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set(x_63, 4, x_62);
lean_ctor_set(x_63, 5, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_20);
x_65 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
lean_inc(x_12);
lean_inc(x_11);
x_66 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_63, x_64, x_65, x_62, x_9, x_10, x_11, x_12, x_59);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = l_Lean_Elab_Tactic_replaceMainGoal(x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_67);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_80 = x_66;
} else {
 lean_dec_ref(x_66);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
lean_dec(x_23);
x_83 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
lean_inc(x_22);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_22);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
x_86 = l_Lean_Syntax_node2(x_22, x_85, x_84, x_2);
x_87 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__9;
x_88 = 1;
lean_inc(x_11);
x_89 = l_Lean_log___at_Lean_Meta_reportDiag___spec__1(x_87, x_88, x_21, x_9, x_10, x_11, x_12, x_82);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_94);
lean_ctor_set(x_95, 4, x_94);
lean_ctor_set(x_95, 5, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_20);
x_97 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
lean_inc(x_12);
lean_inc(x_11);
x_98 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_95, x_96, x_97, x_94, x_9, x_10, x_11, x_12, x_90);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_101 = l_Lean_Elab_Tactic_replaceMainGoal(x_100, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_99);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_108 = x_101;
} else {
 lean_dec_ref(x_101);
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
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_110 = lean_ctor_get(x_98, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_98, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_112 = x_98;
} else {
 lean_dec_ref(x_98);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_ctor_get(x_17, 1);
lean_inc(x_114);
lean_dec(x_17);
x_115 = lean_ctor_get(x_18, 0);
lean_inc(x_115);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_116 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(x_115, x_4, x_9, x_10, x_11, x_12, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_box(0);
x_119 = l_Lean_Elab_Tactic_replaceMainGoal(x_118, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_117);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_dec(x_121);
x_122 = lean_box(0);
lean_ctor_set(x_119, 0, x_122);
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_dec(x_119);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_119);
if (x_126 == 0)
{
return x_119;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_119, 0);
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_119);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_130 = !lean_is_exclusive(x_116);
if (x_130 == 0)
{
return x_116;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_116, 0);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_116);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_17);
if (x_134 == 0)
{
return x_17;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_17, 0);
x_136 = lean_ctor_get(x_17, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_17);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_14);
if (x_138 == 0)
{
return x_14;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_14, 0);
x_140 = lean_ctor_get(x_14, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_14);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
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
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__4;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("str", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
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
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
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
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_25;
}
else
{
lean_object* x_26; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_TSyntax_getString(x_22);
lean_dec(x_22);
lean_inc(x_4);
lean_inc(x_27);
x_30 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_29, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___boxed), 13, 4);
lean_closure_set(x_33, 0, x_27);
lean_closure_set(x_33, 1, x_17);
lean_closure_set(x_33, 2, x_15);
lean_closure_set(x_33, 3, x_31);
x_34 = l_Lean_Elab_Tactic_withMainContext___rarg(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_27);
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
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
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
lean_dec(x_22);
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
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVDecide", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Frontend", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVCheck", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalBvCheck", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__2;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2;
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3;
x_6 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4;
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5;
x_8 = l_Lean_Name_mkStr7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__2;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6;
x_5 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__8;
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
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck___lambda__3___closed__5);
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
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1___closed__8);
if (builtin) {res = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
