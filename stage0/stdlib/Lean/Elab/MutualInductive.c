// Lean compiler output
// Module: Lean.Elab.MutualInductive
// Imports: Lean.Util.ForEachExprWhere Lean.Util.ReplaceLevel Lean.Util.ReplaceExpr Lean.Util.CollectLevelParams Lean.Meta.Constructions Lean.Meta.CollectFVars Lean.Meta.SizeOf Lean.Meta.Injective Lean.Meta.IndPredBelow Lean.Elab.Command Lean.Elab.ComputedFields Lean.Elab.DefView Lean.Elab.DeclUtil Lean.Elab.Deriving.Basic Lean.Elab.DeclarationRange
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_MutualInductive___hyg_20_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__2;
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__3;
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__6;
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__5;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr;
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__14;
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__10;
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedInductiveElabDescr;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__11;
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__15;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_toCtorIdx___boxed(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__4;
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__8;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_toCtorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_InductiveElabDescr_toCtorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_InductiveElabDescr_noConfusion___rarg___boxed), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_InductiveElabDescr_noConfusion___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_InductiveElabDescr_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_InductiveElabDescr_noConfusion(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedInductiveElabDescr() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Attribute_Builtin_getIdent(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Syntax_getId(x_7);
x_10 = lean_st_ref_get(x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_4, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 6);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Environment_contains(x_13, x_9);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_14);
x_21 = lean_box(0);
lean_inc(x_9);
x_22 = l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(x_7, x_9, x_21, x_3, x_4, x_17);
lean_dec(x_3);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
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
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_ctor_get(x_31, 6);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_contains(x_13, x_9);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_33, sizeof(void*)*2);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
lean_inc(x_9);
x_39 = l_Lean_Elab_addConstInfo___at_Lean_PrettyPrinter_mkFormatterAttribute___spec__1(x_7, x_9, x_38, x_3, x_4, x_32);
lean_dec(x_3);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
return x_6;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("builtin_inductive_elab", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inductive_elab", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("InductiveElabDescr", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__5;
x_2 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__6;
x_3 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__7;
x_4 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Register an elaborator for inductive types", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__3___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__2;
x_2 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__4;
x_3 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__10;
x_4 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__9;
x_5 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__11;
x_6 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__12;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inductiveElabAttr", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__5;
x_2 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__6;
x_3 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__7;
x_4 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__13;
x_3 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__15;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___lambda__3(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_MutualInductive___hyg_20_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_inductiveElabAttr_unsafe__1(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Util_ForEachExprWhere(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Constructions(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SizeOf(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_IndPredBelow(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ComputedFields(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DefView(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_MutualInductive(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExprWhere(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SizeOf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IndPredBelow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ComputedFields(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_instInhabitedInductiveElabDescr = _init_l_Lean_Elab_Command_instInhabitedInductiveElabDescr();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedInductiveElabDescr);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__1 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__1);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__2 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__2);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__3 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__3);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__4 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__4);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__5 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__5);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__6 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__6);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__7 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__7);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__8 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__8);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__9 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__9);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__10 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__10);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__11 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__11);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__12 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__12);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__13 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__13);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__14 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__14);
l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__15 = _init_l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr_unsafe__1___closed__15);
if (builtin) {res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_MutualInductive___hyg_20_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_inductiveElabAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_inductiveElabAttr);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
