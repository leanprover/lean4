// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVTrace
// Imports: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide Lean.Elab.Tactic.BVDecide.Frontend.BVCheck Lean.Elab.Tactic.BVDecide.LRAT.Trim Lean.Meta.Tactic.TryThis Std.Tactic.BVDecide.Syntax
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
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__1;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lambda__1___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__8;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4;
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5;
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1;
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3;
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__6;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__8;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not find file name", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not find declaration name", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lrat", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = l_System_FilePath_fileName(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2;
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Elab_Term_getDeclName_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4;
x_17 = l_Lean_throwError___at_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir___spec__1(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = l_Lean_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(x_5, x_6, x_18);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_FileMap_toPosition(x_20, x_23);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
x_26 = lean_string_append(x_25, x_12);
lean_dec(x_12);
x_27 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6;
x_28 = lean_string_append(x_26, x_27);
x_29 = 1;
x_30 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__7;
x_31 = l_Lean_Name_toString(x_19, x_29, x_30);
x_32 = lean_string_append(x_28, x_31);
lean_dec(x_31);
x_33 = lean_string_append(x_32, x_27);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_34);
x_36 = lean_string_append(x_33, x_35);
lean_dec(x_35);
x_37 = lean_string_append(x_36, x_27);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__8;
x_42 = lean_string_append(x_40, x_41);
lean_ctor_set(x_21, 0, x_42);
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = l_Lean_FileMap_toPosition(x_20, x_43);
lean_dec(x_43);
x_46 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
x_47 = lean_string_append(x_46, x_12);
lean_dec(x_12);
x_48 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6;
x_49 = lean_string_append(x_47, x_48);
x_50 = 1;
x_51 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__7;
x_52 = l_Lean_Name_toString(x_19, x_50, x_51);
x_53 = lean_string_append(x_49, x_52);
lean_dec(x_52);
x_54 = lean_string_append(x_53, x_48);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
x_56 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_57 = lean_string_append(x_54, x_56);
lean_dec(x_56);
x_58 = lean_string_append(x_57, x_48);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_dec(x_45);
x_60 = l___private_Init_Data_Repr_0__Nat_reprFast(x_59);
x_61 = lean_string_append(x_58, x_60);
lean_dec(x_60);
x_62 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__8;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_44);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvDecide(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvCheck", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bv_check", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 5);
lean_inc(x_14);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_14, x_15);
x_17 = lean_st_ref_get(x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8;
lean_inc(x_16);
lean_ctor_set_tag(x_17, 2);
lean_ctor_set(x_17, 1, x_21);
lean_ctor_set(x_17, 0, x_16);
x_22 = lean_box(2);
x_23 = l_Lean_Syntax_mkStrLit(x_1, x_22);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7;
x_25 = l_Lean_Syntax_node3(x_16, x_24, x_17, x_2, x_23);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_14);
x_31 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_32 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_29, x_30, x_31, x_28, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8;
lean_inc(x_16);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(2);
x_37 = l_Lean_Syntax_mkStrLit(x_1, x_36);
x_38 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7;
x_39 = l_Lean_Syntax_node3(x_16, x_38, x_35, x_2, x_37);
x_40 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_43, 5, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_14);
x_45 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_46 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_43, x_44, x_45, x_42, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_44);
return x_46;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvTrace", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bvNormalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("bv_normalize", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
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
lean_dec(x_1);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
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
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_21 = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 1);
x_26 = 0;
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_26);
lean_inc(x_8);
lean_inc(x_4);
x_27 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_4);
x_30 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_28, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_31);
lean_inc(x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1___boxed), 11, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_34, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_8, 5);
lean_inc(x_40);
x_41 = l_Lean_SourceInfo_fromRef(x_40, x_26);
x_42 = lean_st_ref_get(x_9, x_39);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_42, 1);
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
x_46 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
lean_inc(x_41);
lean_ctor_set_tag(x_42, 2);
lean_ctor_set(x_42, 1, x_46);
lean_ctor_set(x_42, 0, x_41);
x_47 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9;
x_48 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10;
lean_inc(x_41);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_41);
x_50 = l_Lean_Syntax_node1(x_41, x_18, x_49);
x_51 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_52 = l_Lean_Syntax_node2(x_41, x_51, x_42, x_50);
x_53 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_40);
x_58 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_59 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_56, x_57, x_58, x_55, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_57);
lean_dec(x_15);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_42, 1);
lean_inc(x_60);
lean_dec(x_42);
x_61 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
lean_inc(x_41);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_41);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9;
x_64 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10;
lean_inc(x_41);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_41);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
lean_inc(x_41);
x_66 = l_Lean_Syntax_node1(x_41, x_18, x_65);
x_67 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_68 = l_Lean_Syntax_node2(x_41, x_67, x_62, x_66);
x_69 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_71);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set(x_72, 5, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_40);
x_74 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_75 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_72, x_73, x_74, x_71, x_6, x_7, x_8, x_9, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_73);
lean_dec(x_15);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_38);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_38, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_31, 5);
lean_inc(x_78);
lean_dec(x_31);
x_79 = lean_ctor_get_uint8(x_78, sizeof(void*)*2);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_38);
x_80 = lean_ctor_get(x_37, 1);
lean_inc(x_80);
lean_dec(x_37);
x_81 = lean_box(0);
x_82 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_28, x_17, x_15, x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_28);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_37, 1);
lean_inc(x_83);
lean_dec(x_37);
lean_inc(x_4);
x_84 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_System_FilePath_join(x_85, x_28);
x_88 = lean_ctor_get(x_8, 5);
lean_inc(x_88);
x_89 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_87, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11;
x_93 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_90, x_92);
lean_dec(x_90);
x_94 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___spec__4(x_93, x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_87, x_95, x_25, x_96);
lean_dec(x_95);
lean_dec(x_87);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_88);
lean_free_object(x_38);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_28, x_17, x_15, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_99);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_98);
lean_dec(x_15);
lean_dec(x_28);
return x_100;
}
else
{
uint8_t x_101; 
lean_dec(x_28);
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
x_101 = !lean_is_exclusive(x_97);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
x_103 = lean_io_error_to_string(x_102);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_103);
x_104 = l_Lean_MessageData_ofFormat(x_38);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_88);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_97, 0, x_105);
return x_97;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_97, 0);
x_107 = lean_ctor_get(x_97, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_97);
x_108 = lean_io_error_to_string(x_106);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_108);
x_109 = l_Lean_MessageData_ofFormat(x_38);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_88);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_87);
lean_dec(x_28);
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
x_112 = !lean_is_exclusive(x_94);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_94, 0);
x_114 = lean_io_error_to_string(x_113);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_114);
x_115 = l_Lean_MessageData_ofFormat(x_38);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_88);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_94, 0, x_116);
return x_94;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_94, 0);
x_118 = lean_ctor_get(x_94, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_94);
x_119 = lean_io_error_to_string(x_117);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_119);
x_120 = l_Lean_MessageData_ofFormat(x_38);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_88);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_118);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_87);
lean_dec(x_28);
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
x_123 = !lean_is_exclusive(x_89);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_89, 0);
x_125 = lean_io_error_to_string(x_124);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_125);
x_126 = l_Lean_MessageData_ofFormat(x_38);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_88);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_89, 0, x_127);
return x_89;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_89, 0);
x_129 = lean_ctor_get(x_89, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_89);
x_130 = lean_io_error_to_string(x_128);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_130);
x_131 = l_Lean_MessageData_ofFormat(x_38);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_88);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_129);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_free_object(x_38);
lean_dec(x_28);
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
x_134 = !lean_is_exclusive(x_84);
if (x_134 == 0)
{
return x_84;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_84, 0);
x_136 = lean_ctor_get(x_84, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_84);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; uint8_t x_139; 
lean_dec(x_38);
x_138 = lean_ctor_get(x_31, 5);
lean_inc(x_138);
lean_dec(x_31);
x_139 = lean_ctor_get_uint8(x_138, sizeof(void*)*2);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_37, 1);
lean_inc(x_140);
lean_dec(x_37);
x_141 = lean_box(0);
x_142 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_28, x_17, x_15, x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_140);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_28);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_37, 1);
lean_inc(x_143);
lean_dec(x_37);
lean_inc(x_4);
x_144 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_System_FilePath_join(x_145, x_28);
x_148 = lean_ctor_get(x_8, 5);
lean_inc(x_148);
x_149 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_147, x_146);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11;
x_153 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_150, x_152);
lean_dec(x_150);
x_154 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___spec__4(x_153, x_151);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_147, x_155, x_25, x_156);
lean_dec(x_155);
lean_dec(x_147);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_148);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_28, x_17, x_15, x_158, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_159);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_158);
lean_dec(x_15);
lean_dec(x_28);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_28);
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
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_163 = x_157;
} else {
 lean_dec_ref(x_157);
 x_163 = lean_box(0);
}
x_164 = lean_io_error_to_string(x_161);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_MessageData_ofFormat(x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_148);
lean_ctor_set(x_167, 1, x_166);
if (lean_is_scalar(x_163)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_163;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_162);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_147);
lean_dec(x_28);
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
x_169 = lean_ctor_get(x_154, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_154, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_171 = x_154;
} else {
 lean_dec_ref(x_154);
 x_171 = lean_box(0);
}
x_172 = lean_io_error_to_string(x_169);
x_173 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = l_Lean_MessageData_ofFormat(x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_148);
lean_ctor_set(x_175, 1, x_174);
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_170);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_147);
lean_dec(x_28);
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
x_177 = lean_ctor_get(x_149, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_149, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_179 = x_149;
} else {
 lean_dec_ref(x_149);
 x_179 = lean_box(0);
}
x_180 = lean_io_error_to_string(x_177);
x_181 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = l_Lean_MessageData_ofFormat(x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_148);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_178);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_28);
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
x_185 = lean_ctor_get(x_144, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_144, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_187 = x_144;
} else {
 lean_dec_ref(x_144);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_31);
lean_dec(x_28);
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
x_189 = !lean_is_exclusive(x_37);
if (x_189 == 0)
{
return x_37;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_37, 0);
x_191 = lean_ctor_get(x_37, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_37);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_31);
lean_dec(x_28);
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
x_193 = !lean_is_exclusive(x_33);
if (x_193 == 0)
{
return x_33;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_33, 0);
x_195 = lean_ctor_get(x_33, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_33);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_28);
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
x_197 = !lean_is_exclusive(x_30);
if (x_197 == 0)
{
return x_30;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_30, 0);
x_199 = lean_ctor_get(x_30, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_30);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
uint8_t x_201; 
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
x_201 = !lean_is_exclusive(x_27);
if (x_201 == 0)
{
return x_27;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_27, 0);
x_203 = lean_ctor_get(x_27, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_27);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
lean_object* x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; 
x_205 = lean_ctor_get(x_22, 0);
x_206 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 1);
x_207 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 2);
x_208 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 3);
x_209 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 4);
x_210 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 5);
x_211 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 6);
x_212 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 7);
x_213 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 8);
x_214 = lean_ctor_get(x_22, 1);
lean_inc(x_214);
lean_inc(x_205);
lean_dec(x_22);
x_215 = 0;
x_216 = lean_alloc_ctor(0, 2, 9);
lean_ctor_set(x_216, 0, x_205);
lean_ctor_set(x_216, 1, x_214);
lean_ctor_set_uint8(x_216, sizeof(void*)*2, x_215);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 1, x_206);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 2, x_207);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 3, x_208);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 4, x_209);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 5, x_210);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 6, x_211);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 7, x_212);
lean_ctor_set_uint8(x_216, sizeof(void*)*2 + 8, x_213);
lean_inc(x_8);
lean_inc(x_4);
x_217 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_4);
x_220 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_218, x_216, x_4, x_5, x_6, x_7, x_8, x_9, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
lean_inc(x_221);
lean_inc(x_224);
x_226 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1___boxed), 11, 2);
lean_closure_set(x_226, 0, x_224);
lean_closure_set(x_226, 1, x_221);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_227 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_224, x_226, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_221);
lean_dec(x_218);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_8, 5);
lean_inc(x_230);
x_231 = l_Lean_SourceInfo_fromRef(x_230, x_215);
x_232 = lean_st_ref_get(x_9, x_229);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_234 = x_232;
} else {
 lean_dec_ref(x_232);
 x_234 = lean_box(0);
}
x_235 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
lean_inc(x_231);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(2, 2, 0);
} else {
 x_236 = x_234;
 lean_ctor_set_tag(x_236, 2);
}
lean_ctor_set(x_236, 0, x_231);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9;
x_238 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10;
lean_inc(x_231);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_239, 2, x_238);
lean_inc(x_231);
x_240 = l_Lean_Syntax_node1(x_231, x_18, x_239);
x_241 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_242 = l_Lean_Syntax_node2(x_231, x_241, x_236, x_240);
x_243 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_245);
lean_ctor_set(x_246, 3, x_245);
lean_ctor_set(x_246, 4, x_245);
lean_ctor_set(x_246, 5, x_245);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_230);
x_248 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_249 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_246, x_247, x_248, x_245, x_6, x_7, x_8, x_9, x_233);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_247);
lean_dec(x_15);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_250 = x_228;
} else {
 lean_dec_ref(x_228);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_221, 5);
lean_inc(x_251);
lean_dec(x_221);
x_252 = lean_ctor_get_uint8(x_251, sizeof(void*)*2);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_250);
x_253 = lean_ctor_get(x_227, 1);
lean_inc(x_253);
lean_dec(x_227);
x_254 = lean_box(0);
x_255 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_218, x_17, x_15, x_254, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_253);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_218);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_227, 1);
lean_inc(x_256);
lean_dec(x_227);
lean_inc(x_4);
x_257 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = l_System_FilePath_join(x_258, x_218);
x_261 = lean_ctor_get(x_8, 5);
lean_inc(x_261);
x_262 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_260, x_259);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11;
x_266 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_263, x_265);
lean_dec(x_263);
x_267 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_load___spec__4(x_266, x_264);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_260, x_268, x_206, x_269);
lean_dec(x_268);
lean_dec(x_260);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_261);
lean_dec(x_250);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_218, x_17, x_15, x_271, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_272);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_271);
lean_dec(x_15);
lean_dec(x_218);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_218);
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
x_274 = lean_ctor_get(x_270, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_270, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_276 = x_270;
} else {
 lean_dec_ref(x_270);
 x_276 = lean_box(0);
}
x_277 = lean_io_error_to_string(x_274);
if (lean_is_scalar(x_250)) {
 x_278 = lean_alloc_ctor(3, 1, 0);
} else {
 x_278 = x_250;
 lean_ctor_set_tag(x_278, 3);
}
lean_ctor_set(x_278, 0, x_277);
x_279 = l_Lean_MessageData_ofFormat(x_278);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_261);
lean_ctor_set(x_280, 1, x_279);
if (lean_is_scalar(x_276)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_276;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_275);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_260);
lean_dec(x_218);
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
x_282 = lean_ctor_get(x_267, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_267, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_284 = x_267;
} else {
 lean_dec_ref(x_267);
 x_284 = lean_box(0);
}
x_285 = lean_io_error_to_string(x_282);
if (lean_is_scalar(x_250)) {
 x_286 = lean_alloc_ctor(3, 1, 0);
} else {
 x_286 = x_250;
 lean_ctor_set_tag(x_286, 3);
}
lean_ctor_set(x_286, 0, x_285);
x_287 = l_Lean_MessageData_ofFormat(x_286);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_261);
lean_ctor_set(x_288, 1, x_287);
if (lean_is_scalar(x_284)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_284;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_283);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_260);
lean_dec(x_218);
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
x_290 = lean_ctor_get(x_262, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_262, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_292 = x_262;
} else {
 lean_dec_ref(x_262);
 x_292 = lean_box(0);
}
x_293 = lean_io_error_to_string(x_290);
if (lean_is_scalar(x_250)) {
 x_294 = lean_alloc_ctor(3, 1, 0);
} else {
 x_294 = x_250;
 lean_ctor_set_tag(x_294, 3);
}
lean_ctor_set(x_294, 0, x_293);
x_295 = l_Lean_MessageData_ofFormat(x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_261);
lean_ctor_set(x_296, 1, x_295);
if (lean_is_scalar(x_292)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_292;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_291);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_250);
lean_dec(x_218);
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
x_298 = lean_ctor_get(x_257, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_257, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_300 = x_257;
} else {
 lean_dec_ref(x_257);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_221);
lean_dec(x_218);
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
x_302 = lean_ctor_get(x_227, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_227, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_304 = x_227;
} else {
 lean_dec_ref(x_227);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_221);
lean_dec(x_218);
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
x_306 = lean_ctor_get(x_223, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_223, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_308 = x_223;
} else {
 lean_dec_ref(x_223);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_218);
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
x_310 = lean_ctor_get(x_220, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_220, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_312 = x_220;
} else {
 lean_dec_ref(x_220);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_216);
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
x_314 = lean_ctor_get(x_217, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_217, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_316 = x_217;
} else {
 lean_dec_ref(x_217);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
else
{
uint8_t x_318; 
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
x_318 = !lean_is_exclusive(x_21);
if (x_318 == 0)
{
return x_21;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_21, 0);
x_320 = lean_ctor_get(x_21, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_21);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVDecide", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Frontend", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BVTrace", 7, 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalBvTrace", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3;
x_6 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4;
x_7 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5;
x_8 = l_Lean_Name_mkStr7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__7;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6;
x_5 = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__8;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_LRAT_Trim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__9);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__10);
l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__11);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__7);
l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__8);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
