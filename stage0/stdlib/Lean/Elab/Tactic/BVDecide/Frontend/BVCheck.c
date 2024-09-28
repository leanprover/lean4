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
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_9, 5);
lean_inc(x_19);
x_20 = 0;
x_21 = l_Lean_SourceInfo_fromRef(x_19, x_20);
x_22 = lean_st_ref_get(x_10, x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
lean_inc(x_21);
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_21);
x_27 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
x_28 = l_Lean_Syntax_node1(x_21, x_27, x_22);
x_29 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_19);
x_34 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8;
lean_inc(x_10);
lean_inc(x_9);
x_35 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_32, x_33, x_34, x_31, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
x_38 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_37, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_dec(x_22);
x_48 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__7;
lean_inc(x_21);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_21);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__6;
x_51 = l_Lean_Syntax_node1(x_21, x_50, x_49);
x_52 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__2;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_19);
x_57 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__8;
lean_inc(x_10);
lean_inc(x_9);
x_58 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_55, x_56, x_57, x_54, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_evalBvCheck___lambda__1___closed__10;
x_61 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_60, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
lean_dec(x_15);
x_71 = lean_ctor_get(x_17, 0);
lean_inc(x_71);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_72 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_bvCheck(x_71, x_2, x_7, x_8, x_9, x_10, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(0);
x_75 = l_Lean_Elab_Tactic_replaceMainGoal(x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
return x_75;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_75);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_86 = !lean_is_exclusive(x_72);
if (x_86 == 0)
{
return x_72;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_72, 0);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_72);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_15);
if (x_90 == 0)
{
return x_15;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_15, 0);
x_92 = lean_ctor_get(x_15, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_15);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_12);
if (x_94 == 0)
{
return x_12;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_12, 0);
x_96 = lean_ctor_get(x_12, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_12);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
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
