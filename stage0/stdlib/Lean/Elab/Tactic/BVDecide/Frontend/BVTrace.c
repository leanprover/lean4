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
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_sat_trimProofs;
lean_object* l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
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
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__6;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__4;
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getRefPos___at_Lean_Elab_Term_elabPanic___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__5;
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__1;
lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_MVarId_elabFalseOrByContra___spec__1___rarg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__1;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__3;
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName___closed__5;
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__2;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 5);
lean_inc(x_13);
x_14 = 0;
x_15 = l_Lean_SourceInfo_fromRef(x_13, x_14);
x_16 = lean_st_ref_get(x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8;
lean_inc(x_15);
lean_ctor_set_tag(x_16, 2);
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_15);
x_21 = lean_box(2);
x_22 = l_Lean_Syntax_mkStrLit(x_1, x_21);
x_23 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7;
x_24 = l_Lean_Syntax_node2(x_15, x_23, x_16, x_22);
x_25 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_13);
x_30 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_31 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_2, x_28, x_29, x_30, x_27, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_dec(x_16);
x_33 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__8;
lean_inc(x_15);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_box(2);
x_36 = l_Lean_Syntax_mkStrLit(x_1, x_35);
x_37 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__7;
x_38 = l_Lean_Syntax_node2(x_15, x_37, x_34, x_36);
x_39 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_13);
x_44 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_45 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_2, x_42, x_43, x_44, x_41, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_43);
return x_45;
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
x_1 = lean_mk_string_unchecked("bvNormalize", 11, 11);
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
x_1 = lean_mk_string_unchecked("bv_normalize", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_sat_trimProofs;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_LRAT_trim_go___boxed), 2, 0);
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_MVarId_elabFalseOrByContra___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_getLratFileName(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_4);
x_19 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_mkContext(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*6 + 2);
x_24 = 0;
lean_ctor_set_uint8(x_20, sizeof(void*)*6 + 1, x_24);
x_25 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1___boxed), 11, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_26, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_8, 5);
lean_inc(x_32);
x_33 = l_Lean_SourceInfo_fromRef(x_32, x_24);
x_34 = lean_st_ref_get(x_9, x_31);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
lean_inc(x_33);
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 1, x_38);
lean_ctor_set(x_34, 0, x_33);
x_39 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
x_40 = l_Lean_Syntax_node1(x_33, x_39, x_34);
x_41 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_32);
x_46 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_47 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_44, x_45, x_46, x_43, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_45);
lean_dec(x_15);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_dec(x_34);
x_49 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
lean_inc(x_33);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
x_52 = l_Lean_Syntax_node1(x_33, x_51, x_50);
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
lean_ctor_set(x_57, 0, x_32);
x_58 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_59 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_56, x_57, x_58, x_55, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_57);
lean_dec(x_15);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_30, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_dec(x_29);
x_63 = lean_ctor_get(x_8, 2);
lean_inc(x_63);
x_64 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_65 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_63, x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_free_object(x_30);
x_66 = lean_box(0);
x_67 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_17);
return x_67;
}
else
{
lean_object* x_68; 
lean_inc(x_4);
x_68 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_System_FilePath_join(x_69, x_17);
x_72 = lean_ctor_get(x_8, 5);
lean_inc(x_72);
x_73 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_71, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
x_77 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_74, x_76);
lean_dec(x_74);
x_78 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___spec__4(x_77, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_71, x_79, x_23, x_80);
lean_dec(x_79);
lean_dec(x_71);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_72);
lean_free_object(x_30);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_83);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_82);
lean_dec(x_15);
lean_dec(x_17);
return x_84;
}
else
{
uint8_t x_85; 
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
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_io_error_to_string(x_86);
lean_ctor_set_tag(x_30, 3);
lean_ctor_set(x_30, 0, x_87);
x_88 = l_Lean_MessageData_ofFormat(x_30);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_72);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_81, 0, x_89);
return x_81;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_81, 0);
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_81);
x_92 = lean_io_error_to_string(x_90);
lean_ctor_set_tag(x_30, 3);
lean_ctor_set(x_30, 0, x_92);
x_93 = l_Lean_MessageData_ofFormat(x_30);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_72);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_71);
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
x_96 = !lean_is_exclusive(x_78);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_78, 0);
x_98 = lean_io_error_to_string(x_97);
lean_ctor_set_tag(x_30, 3);
lean_ctor_set(x_30, 0, x_98);
x_99 = l_Lean_MessageData_ofFormat(x_30);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_72);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_78, 0, x_100);
return x_78;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_78, 0);
x_102 = lean_ctor_get(x_78, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_78);
x_103 = lean_io_error_to_string(x_101);
lean_ctor_set_tag(x_30, 3);
lean_ctor_set(x_30, 0, x_103);
x_104 = l_Lean_MessageData_ofFormat(x_30);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_72);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_71);
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
x_107 = !lean_is_exclusive(x_73);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_73, 0);
x_109 = lean_io_error_to_string(x_108);
lean_ctor_set_tag(x_30, 3);
lean_ctor_set(x_30, 0, x_109);
x_110 = l_Lean_MessageData_ofFormat(x_30);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_72);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_73, 0, x_111);
return x_73;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_73, 0);
x_113 = lean_ctor_get(x_73, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_73);
x_114 = lean_io_error_to_string(x_112);
lean_ctor_set_tag(x_30, 3);
lean_ctor_set(x_30, 0, x_114);
x_115 = l_Lean_MessageData_ofFormat(x_30);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_72);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_113);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_free_object(x_30);
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
x_118 = !lean_is_exclusive(x_68);
if (x_118 == 0)
{
return x_68;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_68, 0);
x_120 = lean_ctor_get(x_68, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_68);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_30);
x_122 = lean_ctor_get(x_29, 1);
lean_inc(x_122);
lean_dec(x_29);
x_123 = lean_ctor_get(x_8, 2);
lean_inc(x_123);
x_124 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_125 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_123, x_124);
lean_dec(x_123);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_box(0);
x_127 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_122);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_17);
return x_127;
}
else
{
lean_object* x_128; 
lean_inc(x_4);
x_128 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_122);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_System_FilePath_join(x_129, x_17);
x_132 = lean_ctor_get(x_8, 5);
lean_inc(x_132);
x_133 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_131, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
x_137 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_134, x_136);
lean_dec(x_134);
x_138 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___spec__4(x_137, x_135);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_131, x_139, x_23, x_140);
lean_dec(x_139);
lean_dec(x_131);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_132);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_143);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_142);
lean_dec(x_15);
lean_dec(x_17);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
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
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_147 = x_141;
} else {
 lean_dec_ref(x_141);
 x_147 = lean_box(0);
}
x_148 = lean_io_error_to_string(x_145);
x_149 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Lean_MessageData_ofFormat(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_132);
lean_ctor_set(x_151, 1, x_150);
if (lean_is_scalar(x_147)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_147;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_146);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_131);
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
x_153 = lean_ctor_get(x_138, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_138, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_155 = x_138;
} else {
 lean_dec_ref(x_138);
 x_155 = lean_box(0);
}
x_156 = lean_io_error_to_string(x_153);
x_157 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_158 = l_Lean_MessageData_ofFormat(x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_132);
lean_ctor_set(x_159, 1, x_158);
if (lean_is_scalar(x_155)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_155;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_154);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_131);
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
x_161 = lean_ctor_get(x_133, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_133, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_163 = x_133;
} else {
 lean_dec_ref(x_133);
 x_163 = lean_box(0);
}
x_164 = lean_io_error_to_string(x_161);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_MessageData_ofFormat(x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_132);
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
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
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
x_169 = lean_ctor_get(x_128, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_171 = x_128;
} else {
 lean_dec_ref(x_128);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
}
else
{
uint8_t x_173; 
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
x_173 = !lean_is_exclusive(x_29);
if (x_173 == 0)
{
return x_29;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_29, 0);
x_175 = lean_ctor_get(x_29, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_29);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_20);
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
x_177 = !lean_is_exclusive(x_25);
if (x_177 == 0)
{
return x_25;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_25, 0);
x_179 = lean_ctor_get(x_25, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_25);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; uint8_t x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; 
x_181 = lean_ctor_get(x_20, 0);
x_182 = lean_ctor_get(x_20, 1);
x_183 = lean_ctor_get(x_20, 2);
x_184 = lean_ctor_get(x_20, 3);
x_185 = lean_ctor_get(x_20, 4);
x_186 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
x_187 = lean_ctor_get(x_20, 5);
x_188 = lean_ctor_get_uint8(x_20, sizeof(void*)*6 + 2);
lean_inc(x_187);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_20);
x_189 = 0;
x_190 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_190, 0, x_181);
lean_ctor_set(x_190, 1, x_182);
lean_ctor_set(x_190, 2, x_183);
lean_ctor_set(x_190, 3, x_184);
lean_ctor_set(x_190, 4, x_185);
lean_ctor_set(x_190, 5, x_187);
lean_ctor_set_uint8(x_190, sizeof(void*)*6, x_186);
lean_ctor_set_uint8(x_190, sizeof(void*)*6 + 1, x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*6 + 2, x_188);
x_191 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_192);
x_194 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1___boxed), 11, 2);
lean_closure_set(x_194, 0, x_192);
lean_closure_set(x_194, 1, x_190);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_195 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_192, x_194, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_8, 5);
lean_inc(x_198);
x_199 = l_Lean_SourceInfo_fromRef(x_198, x_189);
x_200 = lean_st_ref_get(x_9, x_197);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
x_203 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
lean_inc(x_199);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(2, 2, 0);
} else {
 x_204 = x_202;
 lean_ctor_set_tag(x_204, 2);
}
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
x_206 = l_Lean_Syntax_node1(x_199, x_205, x_204);
x_207 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_209);
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set(x_210, 4, x_209);
lean_ctor_set(x_210, 5, x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_198);
x_212 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_213 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_210, x_211, x_212, x_209, x_6, x_7, x_8, x_9, x_201);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_211);
lean_dec(x_15);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_214 = x_196;
} else {
 lean_dec_ref(x_196);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_195, 1);
lean_inc(x_215);
lean_dec(x_195);
x_216 = lean_ctor_get(x_8, 2);
lean_inc(x_216);
x_217 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_218 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_216, x_217);
lean_dec(x_216);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_214);
x_219 = lean_box(0);
x_220 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_219, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_215);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_17);
return x_220;
}
else
{
lean_object* x_221; 
lean_inc(x_4);
x_221 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_215);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = l_System_FilePath_join(x_222, x_17);
x_225 = lean_ctor_get(x_8, 5);
lean_inc(x_225);
x_226 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_224, x_223);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
x_230 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_227, x_229);
lean_dec(x_227);
x_231 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___spec__4(x_230, x_228);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_224, x_232, x_188, x_233);
lean_dec(x_232);
lean_dec(x_224);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_225);
lean_dec(x_214);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_235, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_236);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_235);
lean_dec(x_15);
lean_dec(x_17);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
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
x_238 = lean_ctor_get(x_234, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_240 = x_234;
} else {
 lean_dec_ref(x_234);
 x_240 = lean_box(0);
}
x_241 = lean_io_error_to_string(x_238);
if (lean_is_scalar(x_214)) {
 x_242 = lean_alloc_ctor(3, 1, 0);
} else {
 x_242 = x_214;
 lean_ctor_set_tag(x_242, 3);
}
lean_ctor_set(x_242, 0, x_241);
x_243 = l_Lean_MessageData_ofFormat(x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_225);
lean_ctor_set(x_244, 1, x_243);
if (lean_is_scalar(x_240)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_240;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_239);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_224);
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
x_246 = lean_ctor_get(x_231, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_231, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_248 = x_231;
} else {
 lean_dec_ref(x_231);
 x_248 = lean_box(0);
}
x_249 = lean_io_error_to_string(x_246);
if (lean_is_scalar(x_214)) {
 x_250 = lean_alloc_ctor(3, 1, 0);
} else {
 x_250 = x_214;
 lean_ctor_set_tag(x_250, 3);
}
lean_ctor_set(x_250, 0, x_249);
x_251 = l_Lean_MessageData_ofFormat(x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_225);
lean_ctor_set(x_252, 1, x_251);
if (lean_is_scalar(x_248)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_248;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_247);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_224);
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
x_254 = lean_ctor_get(x_226, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_226, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_256 = x_226;
} else {
 lean_dec_ref(x_226);
 x_256 = lean_box(0);
}
x_257 = lean_io_error_to_string(x_254);
if (lean_is_scalar(x_214)) {
 x_258 = lean_alloc_ctor(3, 1, 0);
} else {
 x_258 = x_214;
 lean_ctor_set_tag(x_258, 3);
}
lean_ctor_set(x_258, 0, x_257);
x_259 = l_Lean_MessageData_ofFormat(x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_225);
lean_ctor_set(x_260, 1, x_259);
if (lean_is_scalar(x_256)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_256;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_255);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_214);
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
x_262 = lean_ctor_get(x_221, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_221, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_264 = x_221;
} else {
 lean_dec_ref(x_221);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
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
x_266 = lean_ctor_get(x_195, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_195, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_268 = x_195;
} else {
 lean_dec_ref(x_195);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_190);
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
x_270 = lean_ctor_get(x_191, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_191, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_272 = x_191;
} else {
 lean_dec_ref(x_191);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
else
{
uint8_t x_274; 
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
x_274 = !lean_is_exclusive(x_19);
if (x_274 == 0)
{
return x_19;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_19, 0);
x_276 = lean_ctor_get(x_19, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_19);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_278 = !lean_is_exclusive(x_16);
if (x_278 == 0)
{
return x_16;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_16, 0);
x_280 = lean_ctor_get(x_16, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_16);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
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
