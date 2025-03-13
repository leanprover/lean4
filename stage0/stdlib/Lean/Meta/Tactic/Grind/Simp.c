// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Simp
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.MarkNestedProofs Lean.Meta.Tactic.Grind.Canon
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
lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__5;
lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_preprocess___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__2;
lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markNestedProofsImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_simpCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__7;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__13;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__4;
lean_object* l_Lean_Meta_Grind_unfoldReducible___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__9;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_simpCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__10;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Elab_Term_exposeLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_preprocess___closed__1;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__14;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__3;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__6;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__8;
static lean_object* l_Lean_Meta_Grind_preprocess___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_simpCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_simp(x_1, x_14, x_15, x_16, x_13, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_st_ref_take(x_4, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 3);
lean_dec(x_26);
lean_ctor_set(x_23, 3, x_21);
x_27 = lean_st_ref_set(x_4, x_23, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_20);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
x_34 = lean_ctor_get(x_23, 2);
x_35 = lean_ctor_get(x_23, 4);
x_36 = lean_ctor_get(x_23, 5);
x_37 = lean_ctor_get(x_23, 6);
x_38 = lean_ctor_get(x_23, 7);
x_39 = lean_ctor_get(x_23, 8);
x_40 = lean_ctor_get(x_23, 9);
x_41 = lean_ctor_get(x_23, 10);
x_42 = lean_ctor_get(x_23, 11);
x_43 = lean_ctor_get(x_23, 12);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_44 = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 3, x_21);
lean_ctor_set(x_44, 4, x_35);
lean_ctor_set(x_44, 5, x_36);
lean_ctor_set(x_44, 6, x_37);
lean_ctor_set(x_44, 7, x_38);
lean_ctor_set(x_44, 8, x_39);
lean_ctor_set(x_44, 9, x_40);
lean_ctor_set(x_44, 10, x_41);
lean_ctor_set(x_44, 11, x_42);
lean_ctor_set(x_44, 12, x_43);
x_45 = lean_st_ref_set(x_4, x_44, x_24);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_20);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_simpCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_simpCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_preprocess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_st_ref_get(x_7, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVarsCore(x_16, x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_7, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_19);
x_25 = lean_st_ref_set(x_7, x_21, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_18);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_21, 1);
x_31 = lean_ctor_get(x_21, 2);
x_32 = lean_ctor_get(x_21, 3);
x_33 = lean_ctor_get(x_21, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set(x_34, 4, x_33);
x_35 = lean_st_ref_set(x_7, x_34, x_22);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
lean_ctor_set(x_1, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_inc(x_16);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__3), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_unfoldReducible___lambda__4___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseIrrelevantMData___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_foldProjs___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_foldProjs___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_normalizeLevels___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__8;
x_2 = l_Lean_Meta_Grind_preprocess___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n===>\n", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_preprocess___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_preprocess___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_preprocess___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_13);
x_15 = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_simpCore(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l_Lean_Meta_Grind_preprocess___closed__1;
x_20 = l_Lean_Meta_Grind_preprocess___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Core_transform___at_Lean_Elab_Term_exposeLevelMVars___spec__1(x_18, x_19, x_20, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_Grind_abstractNestedProofs(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Meta_Grind_markNestedProofsImpl(x_25, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Grind_preprocess___closed__3;
x_31 = l_Lean_Meta_Grind_preprocess___closed__4;
lean_inc(x_9);
lean_inc(x_8);
x_32 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_28, x_30, x_31, x_8, x_9, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Grind_preprocess___closed__5;
x_36 = l_Lean_Meta_Grind_preprocess___closed__6;
x_37 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_38 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_33, x_35, x_36, x_37, x_37, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Grind_preprocess___closed__7;
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_39, x_41, x_31, x_8, x_9, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(x_43, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_46);
x_48 = l_Lean_Meta_Simp_Result_mkEqTrans(x_16, x_46, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_52 = l_Lean_Meta_Grind_replacePreMatchCond(x_51, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_53);
x_55 = l_Lean_Meta_Simp_Result_mkEqTrans(x_49, x_53, x_6, x_7, x_8, x_9, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec(x_53);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_59 = l_Lean_Meta_Grind_canon(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Meta_Grind_shareCommon(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_Lean_Meta_Grind_preprocess___closed__10;
x_67 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_62);
lean_free_object(x_11);
lean_dec(x_13);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_Grind_preprocess___lambda__1(x_56, x_64, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_67, 1);
x_75 = lean_ctor_get(x_67, 0);
lean_dec(x_75);
x_76 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_MessageData_ofExpr(x_13);
x_79 = l_Lean_Meta_Grind_preprocess___closed__12;
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_78);
lean_ctor_set(x_67, 0, x_79);
x_80 = l_Lean_Meta_Grind_preprocess___closed__14;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_80);
lean_ctor_set(x_62, 0, x_67);
lean_inc(x_64);
x_81 = l_Lean_MessageData_ofExpr(x_64);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_81);
lean_ctor_set(x_11, 0, x_62);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_79);
x_83 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_66, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_Grind_preprocess___lambda__1(x_56, x_64, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_84);
return x_86;
}
else
{
uint8_t x_87; 
lean_free_object(x_67);
lean_free_object(x_62);
lean_dec(x_64);
lean_dec(x_56);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_76);
if (x_87 == 0)
{
return x_76;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_76, 0);
x_89 = lean_ctor_get(x_76, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_76);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_67, 1);
lean_inc(x_91);
lean_dec(x_67);
x_92 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_MessageData_ofExpr(x_13);
x_95 = l_Lean_Meta_Grind_preprocess___closed__12;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l_Lean_Meta_Grind_preprocess___closed__14;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_97);
lean_ctor_set(x_62, 0, x_96);
lean_inc(x_64);
x_98 = l_Lean_MessageData_ofExpr(x_64);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_98);
lean_ctor_set(x_11, 0, x_62);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_11);
lean_ctor_set(x_99, 1, x_95);
x_100 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_66, x_99, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Meta_Grind_preprocess___lambda__1(x_56, x_64, x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_free_object(x_62);
lean_dec(x_64);
lean_dec(x_56);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_92, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_106 = x_92;
} else {
 lean_dec_ref(x_92);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_108 = lean_ctor_get(x_62, 0);
x_109 = lean_ctor_get(x_62, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_62);
x_110 = l_Lean_Meta_Grind_preprocess___closed__10;
x_111 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_110, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_109);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_free_object(x_11);
lean_dec(x_13);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_box(0);
x_116 = l_Lean_Meta_Grind_preprocess___lambda__1(x_56, x_108, x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = l_Lean_MessageData_ofExpr(x_13);
x_122 = l_Lean_Meta_Grind_preprocess___closed__12;
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_118;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Meta_Grind_preprocess___closed__14;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
lean_inc(x_108);
x_126 = l_Lean_MessageData_ofExpr(x_108);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_126);
lean_ctor_set(x_11, 0, x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_11);
lean_ctor_set(x_127, 1, x_122);
x_128 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_110, x_127, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_120);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Meta_Grind_preprocess___lambda__1(x_56, x_108, x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_130);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_129);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_118);
lean_dec(x_108);
lean_dec(x_56);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = lean_ctor_get(x_119, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_119, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_134 = x_119;
} else {
 lean_dec_ref(x_119);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_56);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_59);
if (x_136 == 0)
{
return x_59;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_59, 0);
x_138 = lean_ctor_get(x_59, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_59);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_53);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_55);
if (x_140 == 0)
{
return x_55;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_55, 0);
x_142 = lean_ctor_get(x_55, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_55);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_49);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_52);
if (x_144 == 0)
{
return x_52;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_52, 0);
x_146 = lean_ctor_get(x_52, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_52);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_46);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_48);
if (x_148 == 0)
{
return x_48;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_48, 0);
x_150 = lean_ctor_get(x_48, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_48);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_45);
if (x_152 == 0)
{
return x_45;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_45, 0);
x_154 = lean_ctor_get(x_45, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_45);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_42);
if (x_156 == 0)
{
return x_42;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_42, 0);
x_158 = lean_ctor_get(x_42, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_42);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_38);
if (x_160 == 0)
{
return x_38;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_38, 0);
x_162 = lean_ctor_get(x_38, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_38);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_32);
if (x_164 == 0)
{
return x_32;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_32, 0);
x_166 = lean_ctor_get(x_32, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_32);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_27);
if (x_168 == 0)
{
return x_27;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_27, 0);
x_170 = lean_ctor_get(x_27, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_27);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_172 = !lean_is_exclusive(x_24);
if (x_172 == 0)
{
return x_24;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_24, 0);
x_174 = lean_ctor_get(x_24, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_24);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_16);
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_21);
if (x_176 == 0)
{
return x_21;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_21, 0);
x_178 = lean_ctor_get(x_21, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_21);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_15);
if (x_180 == 0)
{
return x_15;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_15, 0);
x_182 = lean_ctor_get(x_15, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_15);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_11, 0);
x_185 = lean_ctor_get(x_11, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_184);
x_186 = l___private_Lean_Meta_Tactic_Grind_Simp_0__Lean_Meta_Grind_simpCore(x_184, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = l_Lean_Meta_Grind_preprocess___closed__1;
x_191 = l_Lean_Meta_Grind_preprocess___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_192 = l_Lean_Core_transform___at_Lean_Elab_Term_exposeLevelMVars___spec__1(x_189, x_190, x_191, x_6, x_7, x_8, x_9, x_188);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_195 = l_Lean_Meta_Grind_abstractNestedProofs(x_193, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_198 = l_Lean_Meta_Grind_markNestedProofsImpl(x_196, x_6, x_7, x_8, x_9, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_Meta_Grind_preprocess___closed__3;
x_202 = l_Lean_Meta_Grind_preprocess___closed__4;
lean_inc(x_9);
lean_inc(x_8);
x_203 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_199, x_201, x_202, x_8, x_9, x_200);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_Lean_Meta_Grind_preprocess___closed__5;
x_207 = l_Lean_Meta_Grind_preprocess___closed__6;
x_208 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_209 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_204, x_206, x_207, x_208, x_208, x_6, x_7, x_8, x_9, x_205);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Meta_Grind_preprocess___closed__7;
lean_inc(x_9);
lean_inc(x_8);
x_213 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_210, x_212, x_202, x_8, x_9, x_211);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_216 = l_Lean_Meta_Grind_eraseSimpMatchDiscrsOnly(x_214, x_6, x_7, x_8, x_9, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_217);
x_219 = l_Lean_Meta_Simp_Result_mkEqTrans(x_187, x_217, x_6, x_7, x_8, x_9, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
lean_dec(x_217);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_223 = l_Lean_Meta_Grind_replacePreMatchCond(x_222, x_6, x_7, x_8, x_9, x_221);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_224);
x_226 = l_Lean_Meta_Simp_Result_mkEqTrans(x_220, x_224, x_6, x_7, x_8, x_9, x_225);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_224, 0);
lean_inc(x_229);
lean_dec(x_224);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_230 = l_Lean_Meta_Grind_canon(x_229, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_228);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_Meta_Grind_shareCommon(x_231, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_232);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
x_237 = l_Lean_Meta_Grind_preprocess___closed__10;
x_238 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Grind_updateLastTag___spec__1(x_237, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_235);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_236);
lean_dec(x_184);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_box(0);
x_243 = l_Lean_Meta_Grind_preprocess___lambda__1(x_227, x_234, x_242, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_241);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_238, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_245 = x_238;
} else {
 lean_dec_ref(x_238);
 x_245 = lean_box(0);
}
x_246 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_244);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_248 = l_Lean_MessageData_ofExpr(x_184);
x_249 = l_Lean_Meta_Grind_preprocess___closed__12;
if (lean_is_scalar(x_245)) {
 x_250 = lean_alloc_ctor(7, 2, 0);
} else {
 x_250 = x_245;
 lean_ctor_set_tag(x_250, 7);
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Lean_Meta_Grind_preprocess___closed__14;
if (lean_is_scalar(x_236)) {
 x_252 = lean_alloc_ctor(7, 2, 0);
} else {
 x_252 = x_236;
 lean_ctor_set_tag(x_252, 7);
}
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_inc(x_234);
x_253 = l_Lean_MessageData_ofExpr(x_234);
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_249);
x_256 = l_Lean_addTrace___at_Lean_Meta_Grind_updateLastTag___spec__2(x_237, x_255, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_247);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = l_Lean_Meta_Grind_preprocess___lambda__1(x_227, x_234, x_257, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_258);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_257);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_245);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_227);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_260 = lean_ctor_get(x_246, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_246, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_262 = x_246;
} else {
 lean_dec_ref(x_246);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_227);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_264 = lean_ctor_get(x_230, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_230, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_266 = x_230;
} else {
 lean_dec_ref(x_230);
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
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_224);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_268 = lean_ctor_get(x_226, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_226, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_270 = x_226;
} else {
 lean_dec_ref(x_226);
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
lean_dec(x_220);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_272 = lean_ctor_get(x_223, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_223, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_274 = x_223;
} else {
 lean_dec_ref(x_223);
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
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_217);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_276 = lean_ctor_get(x_219, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_219, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_278 = x_219;
} else {
 lean_dec_ref(x_219);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_280 = lean_ctor_get(x_216, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_216, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_282 = x_216;
} else {
 lean_dec_ref(x_216);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_284 = lean_ctor_get(x_213, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_213, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_286 = x_213;
} else {
 lean_dec_ref(x_213);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_288 = lean_ctor_get(x_209, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_209, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_290 = x_209;
} else {
 lean_dec_ref(x_209);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_292 = lean_ctor_get(x_203, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_203, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_294 = x_203;
} else {
 lean_dec_ref(x_203);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_296 = lean_ctor_get(x_198, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_198, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_298 = x_198;
} else {
 lean_dec_ref(x_198);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_300 = lean_ctor_get(x_195, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_195, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_302 = x_195;
} else {
 lean_dec_ref(x_195);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_304 = lean_ctor_get(x_192, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_192, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_306 = x_192;
} else {
 lean_dec_ref(x_192);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_184);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_308 = lean_ctor_get(x_186, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_186, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_310 = x_186;
} else {
 lean_dec_ref(x_186);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_preprocess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_preprocess___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_preprocess___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedProofs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_preprocess___closed__1 = _init_l_Lean_Meta_Grind_preprocess___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__1);
l_Lean_Meta_Grind_preprocess___closed__2 = _init_l_Lean_Meta_Grind_preprocess___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__2);
l_Lean_Meta_Grind_preprocess___closed__3 = _init_l_Lean_Meta_Grind_preprocess___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__3);
l_Lean_Meta_Grind_preprocess___closed__4 = _init_l_Lean_Meta_Grind_preprocess___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__4);
l_Lean_Meta_Grind_preprocess___closed__5 = _init_l_Lean_Meta_Grind_preprocess___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__5);
l_Lean_Meta_Grind_preprocess___closed__6 = _init_l_Lean_Meta_Grind_preprocess___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__6);
l_Lean_Meta_Grind_preprocess___closed__7 = _init_l_Lean_Meta_Grind_preprocess___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__7);
l_Lean_Meta_Grind_preprocess___closed__8 = _init_l_Lean_Meta_Grind_preprocess___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__8);
l_Lean_Meta_Grind_preprocess___closed__9 = _init_l_Lean_Meta_Grind_preprocess___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__9);
l_Lean_Meta_Grind_preprocess___closed__10 = _init_l_Lean_Meta_Grind_preprocess___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__10);
l_Lean_Meta_Grind_preprocess___closed__11 = _init_l_Lean_Meta_Grind_preprocess___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__11);
l_Lean_Meta_Grind_preprocess___closed__12 = _init_l_Lean_Meta_Grind_preprocess___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__12);
l_Lean_Meta_Grind_preprocess___closed__13 = _init_l_Lean_Meta_Grind_preprocess___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__13);
l_Lean_Meta_Grind_preprocess___closed__14 = _init_l_Lean_Meta_Grind_preprocess___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_preprocess___closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
