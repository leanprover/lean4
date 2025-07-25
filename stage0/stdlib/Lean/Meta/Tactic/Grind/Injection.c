// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injection
// Imports: Lean.Meta.CtorRecognizer Lean.Meta.Tactic.Util Lean.Meta.Tactic.Clear
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
lean_object* l_Lean_Meta_isConstructorAppCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_injection_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_injection_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1;
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* _init_l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_7, 7);
x_13 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0;
x_14 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1;
x_15 = l_Lean_PersistentHashMap_insert___redArg(x_13, x_14, x_12, x_1, x_2);
lean_ctor_set(x_7, 7, x_15);
x_16 = lean_st_ref_set(x_3, x_6, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
x_27 = lean_ctor_get(x_7, 4);
x_28 = lean_ctor_get(x_7, 5);
x_29 = lean_ctor_get(x_7, 6);
x_30 = lean_ctor_get(x_7, 7);
x_31 = lean_ctor_get(x_7, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_32 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0;
x_33 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1;
x_34 = l_Lean_PersistentHashMap_insert___redArg(x_32, x_33, x_30, x_1, x_2);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_28);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_34);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_6, 0, x_35);
x_36 = lean_st_ref_set(x_3, x_6, x_8);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_41 = lean_ctor_get(x_6, 1);
x_42 = lean_ctor_get(x_6, 2);
x_43 = lean_ctor_get(x_6, 3);
x_44 = lean_ctor_get(x_6, 4);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_7, 5);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_7, 6);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_7, 7);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_7, 8);
lean_inc_ref(x_53);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_54 = x_7;
} else {
 lean_dec_ref(x_7);
 x_54 = lean_box(0);
}
x_55 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0;
x_56 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1;
x_57 = l_Lean_PersistentHashMap_insert___redArg(x_55, x_56, x_52, x_1, x_2);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 9, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_50);
lean_ctor_set(x_58, 6, x_51);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_53);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_43);
lean_ctor_set(x_59, 4, x_44);
x_60 = lean_st_ref_set(x_3, x_59, x_8);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_injection_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_injection_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_injection_x3f_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getDecl___redArg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_15 = l_Lean_LocalDecl_type(x_9);
lean_dec(x_9);
x_16 = l_Lean_Expr_cleanupAnnotations(x_15);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_16);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc_ref(x_18);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1;
x_24 = l_Lean_Expr_isConstOf(x_22, x_23);
lean_dec_ref(x_22);
if (x_24 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_11);
x_25 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_18);
x_26 = l_Lean_Meta_isConstructorAppCore_x3f___redArg(x_25, x_6, x_10);
lean_dec_ref(x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_16);
x_31 = l_Lean_Meta_isConstructorAppCore_x3f___redArg(x_30, x_6, x_29);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_32);
lean_free_object(x_26);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_101;
}
else
{
if (lean_obj_tag(x_32) == 0)
{
lean_free_object(x_26);
lean_dec_ref(x_28);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_34);
x_102 = lean_ctor_get(x_28, 0);
lean_inc(x_102);
lean_dec_ref(x_28);
x_103 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_32, 0);
lean_inc(x_104);
lean_dec_ref(x_32);
x_105 = lean_ctor_get(x_104, 0);
lean_inc_ref(x_105);
lean_dec(x_104);
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
lean_dec_ref(x_103);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_name_eq(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
if (x_24 == 0)
{
lean_free_object(x_26);
goto block_98;
}
else
{
lean_object* x_109; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_box(0);
lean_ctor_set(x_26, 1, x_33);
lean_ctor_set(x_26, 0, x_109);
return x_26;
}
}
else
{
lean_free_object(x_26);
goto block_98;
}
}
}
block_98:
{
lean_object* x_35; 
lean_inc(x_2);
x_35 = l_Lean_MVarId_getType(x_2, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
lean_inc(x_1);
x_38 = l_Lean_mkFVar(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_39 = l_Lean_Meta_mkNoConfusion(x_36, x_38, x_3, x_4, x_5, x_6, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_40);
x_42 = lean_infer_type(x_40, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_45 = l_Lean_Meta_whnfD(x_43, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 7)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_48);
lean_dec_ref(x_46);
lean_inc(x_2);
x_49 = l_Lean_MVarId_getTag(x_2, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = l_Lean_Expr_headBeta(x_48);
lean_inc_ref(x_3);
x_53 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_52, x_50, x_3, x_4, x_5, x_6, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
lean_inc(x_54);
x_56 = l_Lean_mkApp(x_40, x_54);
x_57 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg(x_2, x_56, x_4, x_55);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_Expr_mvarId_x21(x_54);
lean_dec(x_54);
x_60 = l_Lean_MVarId_clear(x_59, x_1, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_60);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec_ref(x_48);
lean_dec(x_40);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_49);
if (x_72 == 0)
{
return x_49;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_49, 0);
x_74 = lean_ctor_get(x_49, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_49);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_46);
lean_dec(x_40);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_45);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_45, 0);
lean_dec(x_77);
x_78 = lean_box(0);
lean_ctor_set(x_45, 0, x_78);
return x_45;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_45, 1);
lean_inc(x_79);
lean_dec(x_45);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_40);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_45);
if (x_82 == 0)
{
return x_45;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_45, 0);
x_84 = lean_ctor_get(x_45, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_45);
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
lean_dec(x_40);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_42);
if (x_86 == 0)
{
return x_42;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_42, 0);
x_88 = lean_ctor_get(x_42, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_42);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_39);
if (x_90 == 0)
{
return x_39;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_39, 0);
x_92 = lean_ctor_get(x_39, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_39);
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
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_35);
if (x_94 == 0)
{
return x_35;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_35, 0);
x_96 = lean_ctor_get(x_35, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_35);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
block_101:
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_34;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_33);
return x_100;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_26, 0);
x_111 = lean_ctor_get(x_26, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_26);
x_112 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_112);
lean_dec_ref(x_16);
x_113 = l_Lean_Meta_isConstructorAppCore_x3f___redArg(x_112, x_6, x_111);
lean_dec_ref(x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_obj_tag(x_110) == 0)
{
lean_dec(x_114);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_179;
}
else
{
if (lean_obj_tag(x_114) == 0)
{
lean_dec_ref(x_110);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_dec(x_116);
x_180 = lean_ctor_get(x_110, 0);
lean_inc(x_180);
lean_dec_ref(x_110);
x_181 = lean_ctor_get(x_180, 0);
lean_inc_ref(x_181);
lean_dec(x_180);
x_182 = lean_ctor_get(x_114, 0);
lean_inc(x_182);
lean_dec_ref(x_114);
x_183 = lean_ctor_get(x_182, 0);
lean_inc_ref(x_183);
lean_dec(x_182);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
lean_dec_ref(x_181);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
lean_dec_ref(x_183);
x_186 = lean_name_eq(x_184, x_185);
lean_dec(x_185);
lean_dec(x_184);
if (x_186 == 0)
{
if (x_24 == 0)
{
goto block_176;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_115);
return x_188;
}
}
else
{
goto block_176;
}
}
}
block_176:
{
lean_object* x_117; 
lean_inc(x_2);
x_117 = l_Lean_MVarId_getType(x_2, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
lean_inc(x_1);
x_120 = l_Lean_mkFVar(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_121 = l_Lean_Meta_mkNoConfusion(x_118, x_120, x_3, x_4, x_5, x_6, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_122);
x_124 = lean_infer_type(x_122, x_3, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_127 = l_Lean_Meta_whnfD(x_125, x_3, x_4, x_5, x_6, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 7)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = lean_ctor_get(x_128, 1);
lean_inc_ref(x_130);
lean_dec_ref(x_128);
lean_inc(x_2);
x_131 = l_Lean_MVarId_getTag(x_2, x_3, x_4, x_5, x_6, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec_ref(x_131);
x_134 = l_Lean_Expr_headBeta(x_130);
lean_inc_ref(x_3);
x_135 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_134, x_132, x_3, x_4, x_5, x_6, x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec_ref(x_135);
lean_inc(x_136);
x_138 = l_Lean_mkApp(x_122, x_136);
x_139 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg(x_2, x_138, x_4, x_137);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = l_Lean_Expr_mvarId_x21(x_136);
lean_dec(x_136);
x_142 = l_Lean_MVarId_clear(x_141, x_1, x_3, x_4, x_5, x_6, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_143);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_142, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_142, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_150 = x_142;
} else {
 lean_dec_ref(x_142);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_130);
lean_dec(x_122);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_ctor_get(x_131, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_131, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_154 = x_131;
} else {
 lean_dec_ref(x_131);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_128);
lean_dec(x_122);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_127, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_157 = x_127;
} else {
 lean_dec_ref(x_127);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_122);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_127, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_127, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_162 = x_127;
} else {
 lean_dec_ref(x_127);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_122);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_124, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_124, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_166 = x_124;
} else {
 lean_dec_ref(x_124);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_121, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_121, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_170 = x_121;
} else {
 lean_dec_ref(x_121);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_ctor_get(x_117, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_117, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_174 = x_117;
} else {
 lean_dec_ref(x_117);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
block_179:
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_116;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_115);
return x_178;
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_11;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_189; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_8);
if (x_189 == 0)
{
return x_8;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_8, 0);
x_191 = lean_ctor_get(x_8, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_8);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_injection_x3f___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_injection_x3f_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0 = _init_l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__0);
l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1 = _init_l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_MVarId_assign___at___Lean_Meta_Grind_injection_x3f_spec__0___redArg___closed__1);
l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0 = _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0);
l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1 = _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
