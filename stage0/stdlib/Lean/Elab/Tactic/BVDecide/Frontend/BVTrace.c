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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_8, 5);
lean_inc(x_33);
x_34 = l_Lean_SourceInfo_fromRef(x_33, x_24);
x_35 = lean_st_ref_get(x_9, x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
lean_inc(x_34);
lean_ctor_set_tag(x_35, 2);
lean_ctor_set(x_35, 1, x_39);
lean_ctor_set(x_35, 0, x_34);
x_40 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
x_41 = l_Lean_Syntax_node1(x_34, x_40, x_35);
x_42 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_33);
x_47 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_48 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_45, x_46, x_47, x_44, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_46);
lean_dec(x_15);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_dec(x_35);
x_50 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
lean_inc(x_34);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_34);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
x_53 = l_Lean_Syntax_node1(x_34, x_52, x_51);
x_54 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_56);
lean_ctor_set(x_57, 5, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_33);
x_59 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_60 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_57, x_58, x_59, x_56, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_58);
lean_dec(x_15);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_31);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_31, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_29, 1);
lean_inc(x_63);
lean_dec(x_29);
x_64 = lean_ctor_get(x_8, 2);
lean_inc(x_64);
x_65 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_66 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_free_object(x_31);
x_67 = lean_box(0);
x_68 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_17);
return x_68;
}
else
{
lean_object* x_69; 
lean_inc(x_4);
x_69 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_System_FilePath_join(x_70, x_17);
x_73 = lean_ctor_get(x_8, 5);
lean_inc(x_73);
x_74 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_72, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
x_78 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_75, x_77);
lean_dec(x_75);
x_79 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___spec__4(x_78, x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_72, x_80, x_23, x_81);
lean_dec(x_80);
lean_dec(x_72);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_73);
lean_free_object(x_31);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_83);
lean_dec(x_15);
lean_dec(x_17);
return x_85;
}
else
{
uint8_t x_86; 
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
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_io_error_to_string(x_87);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_88);
x_89 = l_Lean_MessageData_ofFormat(x_31);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_73);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_82, 0, x_90);
return x_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_82);
x_93 = lean_io_error_to_string(x_91);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_93);
x_94 = l_Lean_MessageData_ofFormat(x_31);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_73);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_72);
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
x_97 = !lean_is_exclusive(x_79);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_79, 0);
x_99 = lean_io_error_to_string(x_98);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_99);
x_100 = l_Lean_MessageData_ofFormat(x_31);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_73);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_79, 0, x_101);
return x_79;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_79, 0);
x_103 = lean_ctor_get(x_79, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_79);
x_104 = lean_io_error_to_string(x_102);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_104);
x_105 = l_Lean_MessageData_ofFormat(x_31);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_73);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_72);
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
x_108 = !lean_is_exclusive(x_74);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_74, 0);
x_110 = lean_io_error_to_string(x_109);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_110);
x_111 = l_Lean_MessageData_ofFormat(x_31);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_73);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_74, 0, x_112);
return x_74;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_74, 0);
x_114 = lean_ctor_get(x_74, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_74);
x_115 = lean_io_error_to_string(x_113);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 0, x_115);
x_116 = l_Lean_MessageData_ofFormat(x_31);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_73);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_free_object(x_31);
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
x_119 = !lean_is_exclusive(x_69);
if (x_119 == 0)
{
return x_69;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_69, 0);
x_121 = lean_ctor_get(x_69, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_69);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_31);
x_123 = lean_ctor_get(x_29, 1);
lean_inc(x_123);
lean_dec(x_29);
x_124 = lean_ctor_get(x_8, 2);
lean_inc(x_124);
x_125 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_126 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_124, x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_box(0);
x_128 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_127, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_123);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_17);
return x_128;
}
else
{
lean_object* x_129; 
lean_inc(x_4);
x_129 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_123);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_System_FilePath_join(x_130, x_17);
x_133 = lean_ctor_get(x_8, 5);
lean_inc(x_133);
x_134 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_132, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
x_138 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_135, x_137);
lean_dec(x_135);
x_139 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___spec__4(x_138, x_136);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_132, x_140, x_23, x_141);
lean_dec(x_140);
lean_dec(x_132);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_133);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_143, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_143);
lean_dec(x_15);
lean_dec(x_17);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
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
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_io_error_to_string(x_146);
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l_Lean_MessageData_ofFormat(x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_133);
lean_ctor_set(x_152, 1, x_151);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_147);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_132);
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
x_154 = lean_ctor_get(x_139, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_139, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_156 = x_139;
} else {
 lean_dec_ref(x_139);
 x_156 = lean_box(0);
}
x_157 = lean_io_error_to_string(x_154);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = l_Lean_MessageData_ofFormat(x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_133);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_156)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_156;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_155);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_132);
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
x_162 = lean_ctor_get(x_134, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_134, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_164 = x_134;
} else {
 lean_dec_ref(x_134);
 x_164 = lean_box(0);
}
x_165 = lean_io_error_to_string(x_162);
x_166 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = l_Lean_MessageData_ofFormat(x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_133);
lean_ctor_set(x_168, 1, x_167);
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_164;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_163);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
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
x_170 = lean_ctor_get(x_129, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_129, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_172 = x_129;
} else {
 lean_dec_ref(x_129);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
}
else
{
uint8_t x_174; 
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
x_174 = !lean_is_exclusive(x_29);
if (x_174 == 0)
{
return x_29;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_29, 0);
x_176 = lean_ctor_get(x_29, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_29);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
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
x_178 = !lean_is_exclusive(x_25);
if (x_178 == 0)
{
return x_25;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_25, 0);
x_180 = lean_ctor_get(x_25, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_25);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
x_182 = lean_ctor_get(x_20, 0);
x_183 = lean_ctor_get(x_20, 1);
x_184 = lean_ctor_get(x_20, 2);
x_185 = lean_ctor_get(x_20, 3);
x_186 = lean_ctor_get(x_20, 4);
x_187 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
x_188 = lean_ctor_get(x_20, 5);
x_189 = lean_ctor_get_uint8(x_20, sizeof(void*)*6 + 2);
lean_inc(x_188);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_20);
x_190 = 0;
x_191 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_191, 0, x_182);
lean_ctor_set(x_191, 1, x_183);
lean_ctor_set(x_191, 2, x_184);
lean_ctor_set(x_191, 3, x_185);
lean_ctor_set(x_191, 4, x_186);
lean_ctor_set(x_191, 5, x_188);
lean_ctor_set_uint8(x_191, sizeof(void*)*6, x_187);
lean_ctor_set_uint8(x_191, sizeof(void*)*6 + 1, x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*6 + 2, x_189);
x_192 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_193);
x_195 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__1___boxed), 11, 2);
lean_closure_set(x_195, 0, x_193);
lean_closure_set(x_195, 1, x_191);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_196 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_193, x_195, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_ctor_get(x_8, 5);
lean_inc(x_200);
x_201 = l_Lean_SourceInfo_fromRef(x_200, x_190);
x_202 = lean_st_ref_get(x_9, x_199);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
x_205 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__5;
lean_inc(x_201);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(2, 2, 0);
} else {
 x_206 = x_204;
 lean_ctor_set_tag(x_206, 2);
}
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__4;
x_208 = l_Lean_Syntax_node1(x_201, x_207, x_206);
x_209 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__2;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_211);
lean_ctor_set(x_212, 3, x_211);
lean_ctor_set(x_212, 4, x_211);
lean_ctor_set(x_212, 5, x_211);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_200);
x_214 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2___closed__9;
x_215 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_15, x_212, x_213, x_214, x_211, x_6, x_7, x_8, x_9, x_203);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_213);
lean_dec(x_15);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_216 = x_198;
} else {
 lean_dec_ref(x_198);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_196, 1);
lean_inc(x_217);
lean_dec(x_196);
x_218 = lean_ctor_get(x_8, 2);
lean_inc(x_218);
x_219 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__6;
x_220 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_218, x_219);
lean_dec(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_216);
x_221 = lean_box(0);
x_222 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_217);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_15);
lean_dec(x_17);
return x_222;
}
else
{
lean_object* x_223; 
lean_inc(x_4);
x_223 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVCheck_getSrcDir(x_4, x_5, x_6, x_7, x_8, x_9, x_217);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = l_System_FilePath_join(x_224, x_17);
x_227 = lean_ctor_get(x_8, 5);
lean_inc(x_227);
x_228 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_226, x_225);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___closed__7;
x_232 = l_Lean_Elab_Tactic_BVDecide_LRAT_trim_M_run___rarg(x_229, x_231);
lean_dec(x_229);
x_233 = l_IO_ofExcept___at_Lean_Elab_Tactic_BVDecide_Frontend_LratCert_ofFile___spec__4(x_232, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_226, x_234, x_189, x_235);
lean_dec(x_234);
lean_dec(x_226);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_227);
lean_dec(x_216);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l_Lean_Elab_Tactic_BVDecide_Frontend_BVTrace_evalBvTrace___lambda__2(x_17, x_15, x_237, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_238);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_237);
lean_dec(x_15);
lean_dec(x_17);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
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
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_242 = x_236;
} else {
 lean_dec_ref(x_236);
 x_242 = lean_box(0);
}
x_243 = lean_io_error_to_string(x_240);
if (lean_is_scalar(x_216)) {
 x_244 = lean_alloc_ctor(3, 1, 0);
} else {
 x_244 = x_216;
 lean_ctor_set_tag(x_244, 3);
}
lean_ctor_set(x_244, 0, x_243);
x_245 = l_Lean_MessageData_ofFormat(x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_227);
lean_ctor_set(x_246, 1, x_245);
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_241);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_226);
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
x_248 = lean_ctor_get(x_233, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_233, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_250 = x_233;
} else {
 lean_dec_ref(x_233);
 x_250 = lean_box(0);
}
x_251 = lean_io_error_to_string(x_248);
if (lean_is_scalar(x_216)) {
 x_252 = lean_alloc_ctor(3, 1, 0);
} else {
 x_252 = x_216;
 lean_ctor_set_tag(x_252, 3);
}
lean_ctor_set(x_252, 0, x_251);
x_253 = l_Lean_MessageData_ofFormat(x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_227);
lean_ctor_set(x_254, 1, x_253);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_250;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_249);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_226);
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
x_256 = lean_ctor_get(x_228, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_228, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_258 = x_228;
} else {
 lean_dec_ref(x_228);
 x_258 = lean_box(0);
}
x_259 = lean_io_error_to_string(x_256);
if (lean_is_scalar(x_216)) {
 x_260 = lean_alloc_ctor(3, 1, 0);
} else {
 x_260 = x_216;
 lean_ctor_set_tag(x_260, 3);
}
lean_ctor_set(x_260, 0, x_259);
x_261 = l_Lean_MessageData_ofFormat(x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_227);
lean_ctor_set(x_262, 1, x_261);
if (lean_is_scalar(x_258)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_258;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_257);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
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
x_264 = lean_ctor_get(x_223, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_223, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_266 = x_223;
} else {
 lean_dec_ref(x_223);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
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
x_268 = lean_ctor_get(x_196, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_196, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_270 = x_196;
} else {
 lean_dec_ref(x_196);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_191);
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
x_272 = lean_ctor_get(x_192, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_192, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_274 = x_192;
} else {
 lean_dec_ref(x_192);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
}
else
{
uint8_t x_276; 
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
x_276 = !lean_is_exclusive(x_19);
if (x_276 == 0)
{
return x_19;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_19, 0);
x_278 = lean_ctor_get(x_19, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_19);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_280 = !lean_is_exclusive(x_16);
if (x_280 == 0)
{
return x_16;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_16, 0);
x_282 = lean_ctor_get(x_16, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_16);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
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
