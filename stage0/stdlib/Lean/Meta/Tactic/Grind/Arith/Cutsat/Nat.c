// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
// Imports: Init.Data.Int.OfNat Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Simp.Arith.Nat.Basic Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulNat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__0;
static lean_object* l_Int_OfNat_toExpr___closed__8;
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__3;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__6;
LEAN_EXPORT lean_object* l_Int_OfNat_toIntEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__2;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__15;
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5;
static lean_object* l_Int_OfNat_toExpr___closed__7;
lean_object* l_Lean_mkIntDiv(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__0;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_mkIntMod(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__4;
static lean_object* l_Int_OfNat_toExpr___closed__11;
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__19;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_isInstHPowNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__3;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1;
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__14;
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0;
static lean_object* l_Int_OfNat_toExpr___closed__17;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__5;
static lean_object* l_Int_OfNat_toExpr___closed__4;
static lean_object* l_Int_OfNat_toExpr___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_instToExprExpr___closed__0;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__4;
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toOfNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__13;
static lean_object* l_Int_OfNat_toExpr___closed__23;
static lean_object* l_Int_OfNat_toExpr___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1;
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__6;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isInstLENat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__1;
static lean_object* l_Int_OfNat_toExpr___closed__9;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__8;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__13;
LEAN_EXPORT lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__16;
static lean_object* l_Int_OfNat_toExpr___closed__21;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
static lean_object* l_Int_OfNat_toIntLe_x3f___closed__1;
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkIntNatCast(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__14;
static lean_object* l_Int_OfNat_toIntLe_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toIntLe_x3f___closed__0;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHAddNat___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__9;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr_go(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__11;
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__7;
lean_object* l_Int_toNat(lean_object*);
static lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__5;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__16;
static lean_object* l_Int_OfNat_toExpr___closed__22;
lean_object* l_Lean_mkIntPowNat(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__0;
static lean_object* l_Int_OfNat_toOfNatExpr___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__10;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr___lam__0(lean_object*);
lean_object* l_Lean_Meta_isInstDvdNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_instToExprExpr___closed__1;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__1;
static lean_object* l_Int_OfNat_toExpr___closed__20;
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHDivInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toExpr___closed__15;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3;
static lean_object* l_Int_OfNat_toIntDvd_x3f___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Int_OfNat_toOfNatExpr___closed__5;
lean_object* l_Lean_Meta_Grind_markAsCutsatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHDivNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_toIntLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHModInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
LEAN_EXPORT lean_object* l_Int_OfNat_toExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_11);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_2, x_19);
x_21 = lean_ctor_get(x_18, 5);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 14);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 2);
lean_inc(x_26);
lean_dec(x_21);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_22, 14);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_23, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 4);
x_33 = lean_ctor_get(x_24, 5);
lean_inc(x_26);
lean_inc(x_1);
x_34 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_32, x_1, x_26);
lean_inc(x_1);
x_35 = l_Lean_PersistentArray_push___redArg(x_33, x_1);
lean_ctor_set(x_24, 5, x_35);
lean_ctor_set(x_24, 4, x_34);
x_36 = lean_st_ref_set(x_2, x_22, x_25);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_26);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
x_49 = lean_ctor_get(x_24, 2);
x_50 = lean_ctor_get(x_24, 3);
x_51 = lean_ctor_get(x_24, 4);
x_52 = lean_ctor_get(x_24, 5);
x_53 = lean_ctor_get(x_24, 6);
x_54 = lean_ctor_get(x_24, 7);
x_55 = lean_ctor_get(x_24, 8);
x_56 = lean_ctor_get(x_24, 9);
x_57 = lean_ctor_get(x_24, 10);
x_58 = lean_ctor_get(x_24, 11);
x_59 = lean_ctor_get(x_24, 12);
x_60 = lean_ctor_get(x_24, 13);
x_61 = lean_ctor_get(x_24, 14);
x_62 = lean_ctor_get(x_24, 15);
x_63 = lean_ctor_get_uint8(x_24, sizeof(void*)*21);
x_64 = lean_ctor_get(x_24, 16);
x_65 = lean_ctor_get(x_24, 17);
x_66 = lean_ctor_get(x_24, 18);
x_67 = lean_ctor_get(x_24, 19);
x_68 = lean_ctor_get(x_24, 20);
x_69 = lean_ctor_get_uint8(x_24, sizeof(void*)*21 + 1);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
lean_inc(x_26);
lean_inc(x_1);
x_70 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_51, x_1, x_26);
lean_inc(x_1);
x_71 = l_Lean_PersistentArray_push___redArg(x_52, x_1);
x_72 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_72, 0, x_47);
lean_ctor_set(x_72, 1, x_48);
lean_ctor_set(x_72, 2, x_49);
lean_ctor_set(x_72, 3, x_50);
lean_ctor_set(x_72, 4, x_70);
lean_ctor_set(x_72, 5, x_71);
lean_ctor_set(x_72, 6, x_53);
lean_ctor_set(x_72, 7, x_54);
lean_ctor_set(x_72, 8, x_55);
lean_ctor_set(x_72, 9, x_56);
lean_ctor_set(x_72, 10, x_57);
lean_ctor_set(x_72, 11, x_58);
lean_ctor_set(x_72, 12, x_59);
lean_ctor_set(x_72, 13, x_60);
lean_ctor_set(x_72, 14, x_61);
lean_ctor_set(x_72, 15, x_62);
lean_ctor_set(x_72, 16, x_64);
lean_ctor_set(x_72, 17, x_65);
lean_ctor_set(x_72, 18, x_66);
lean_ctor_set(x_72, 19, x_67);
lean_ctor_set(x_72, 20, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*21, x_63);
lean_ctor_set_uint8(x_72, sizeof(void*)*21 + 1, x_69);
lean_ctor_set(x_23, 1, x_72);
x_73 = lean_st_ref_set(x_2, x_22, x_25);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_26);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_26);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_83 = lean_ctor_get(x_23, 0);
x_84 = lean_ctor_get(x_23, 2);
x_85 = lean_ctor_get(x_23, 3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_23);
x_86 = lean_ctor_get(x_24, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_24, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_24, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_24, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_24, 4);
lean_inc(x_90);
x_91 = lean_ctor_get(x_24, 5);
lean_inc(x_91);
x_92 = lean_ctor_get(x_24, 6);
lean_inc(x_92);
x_93 = lean_ctor_get(x_24, 7);
lean_inc(x_93);
x_94 = lean_ctor_get(x_24, 8);
lean_inc(x_94);
x_95 = lean_ctor_get(x_24, 9);
lean_inc(x_95);
x_96 = lean_ctor_get(x_24, 10);
lean_inc(x_96);
x_97 = lean_ctor_get(x_24, 11);
lean_inc(x_97);
x_98 = lean_ctor_get(x_24, 12);
lean_inc(x_98);
x_99 = lean_ctor_get(x_24, 13);
lean_inc(x_99);
x_100 = lean_ctor_get(x_24, 14);
lean_inc(x_100);
x_101 = lean_ctor_get(x_24, 15);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_24, sizeof(void*)*21);
x_103 = lean_ctor_get(x_24, 16);
lean_inc(x_103);
x_104 = lean_ctor_get(x_24, 17);
lean_inc(x_104);
x_105 = lean_ctor_get(x_24, 18);
lean_inc(x_105);
x_106 = lean_ctor_get(x_24, 19);
lean_inc(x_106);
x_107 = lean_ctor_get(x_24, 20);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_24, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 lean_ctor_release(x_24, 6);
 lean_ctor_release(x_24, 7);
 lean_ctor_release(x_24, 8);
 lean_ctor_release(x_24, 9);
 lean_ctor_release(x_24, 10);
 lean_ctor_release(x_24, 11);
 lean_ctor_release(x_24, 12);
 lean_ctor_release(x_24, 13);
 lean_ctor_release(x_24, 14);
 lean_ctor_release(x_24, 15);
 lean_ctor_release(x_24, 16);
 lean_ctor_release(x_24, 17);
 lean_ctor_release(x_24, 18);
 lean_ctor_release(x_24, 19);
 lean_ctor_release(x_24, 20);
 x_109 = x_24;
} else {
 lean_dec_ref(x_24);
 x_109 = lean_box(0);
}
lean_inc(x_26);
lean_inc(x_1);
x_110 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_90, x_1, x_26);
lean_inc(x_1);
x_111 = l_Lean_PersistentArray_push___redArg(x_91, x_1);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 21, 2);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_86);
lean_ctor_set(x_112, 1, x_87);
lean_ctor_set(x_112, 2, x_88);
lean_ctor_set(x_112, 3, x_89);
lean_ctor_set(x_112, 4, x_110);
lean_ctor_set(x_112, 5, x_111);
lean_ctor_set(x_112, 6, x_92);
lean_ctor_set(x_112, 7, x_93);
lean_ctor_set(x_112, 8, x_94);
lean_ctor_set(x_112, 9, x_95);
lean_ctor_set(x_112, 10, x_96);
lean_ctor_set(x_112, 11, x_97);
lean_ctor_set(x_112, 12, x_98);
lean_ctor_set(x_112, 13, x_99);
lean_ctor_set(x_112, 14, x_100);
lean_ctor_set(x_112, 15, x_101);
lean_ctor_set(x_112, 16, x_103);
lean_ctor_set(x_112, 17, x_104);
lean_ctor_set(x_112, 18, x_105);
lean_ctor_set(x_112, 19, x_106);
lean_ctor_set(x_112, 20, x_107);
lean_ctor_set_uint8(x_112, sizeof(void*)*21, x_102);
lean_ctor_set_uint8(x_112, sizeof(void*)*21 + 1, x_108);
x_113 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_113, 0, x_83);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_84);
lean_ctor_set(x_113, 3, x_85);
lean_ctor_set(x_22, 14, x_113);
x_114 = lean_st_ref_set(x_2, x_22, x_25);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_26);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_26);
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_122 = x_116;
} else {
 lean_dec_ref(x_116);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_124 = lean_ctor_get(x_22, 0);
x_125 = lean_ctor_get(x_22, 1);
x_126 = lean_ctor_get(x_22, 2);
x_127 = lean_ctor_get(x_22, 3);
x_128 = lean_ctor_get(x_22, 4);
x_129 = lean_ctor_get(x_22, 5);
x_130 = lean_ctor_get(x_22, 6);
x_131 = lean_ctor_get(x_22, 7);
x_132 = lean_ctor_get_uint8(x_22, sizeof(void*)*16);
x_133 = lean_ctor_get(x_22, 8);
x_134 = lean_ctor_get(x_22, 9);
x_135 = lean_ctor_get(x_22, 10);
x_136 = lean_ctor_get(x_22, 11);
x_137 = lean_ctor_get(x_22, 12);
x_138 = lean_ctor_get(x_22, 13);
x_139 = lean_ctor_get(x_22, 15);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_22);
x_140 = lean_ctor_get(x_23, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_23, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_23, 3);
lean_inc(x_142);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 x_143 = x_23;
} else {
 lean_dec_ref(x_23);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_24, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_24, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_24, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_24, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_24, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_24, 5);
lean_inc(x_149);
x_150 = lean_ctor_get(x_24, 6);
lean_inc(x_150);
x_151 = lean_ctor_get(x_24, 7);
lean_inc(x_151);
x_152 = lean_ctor_get(x_24, 8);
lean_inc(x_152);
x_153 = lean_ctor_get(x_24, 9);
lean_inc(x_153);
x_154 = lean_ctor_get(x_24, 10);
lean_inc(x_154);
x_155 = lean_ctor_get(x_24, 11);
lean_inc(x_155);
x_156 = lean_ctor_get(x_24, 12);
lean_inc(x_156);
x_157 = lean_ctor_get(x_24, 13);
lean_inc(x_157);
x_158 = lean_ctor_get(x_24, 14);
lean_inc(x_158);
x_159 = lean_ctor_get(x_24, 15);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_24, sizeof(void*)*21);
x_161 = lean_ctor_get(x_24, 16);
lean_inc(x_161);
x_162 = lean_ctor_get(x_24, 17);
lean_inc(x_162);
x_163 = lean_ctor_get(x_24, 18);
lean_inc(x_163);
x_164 = lean_ctor_get(x_24, 19);
lean_inc(x_164);
x_165 = lean_ctor_get(x_24, 20);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_24, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 lean_ctor_release(x_24, 6);
 lean_ctor_release(x_24, 7);
 lean_ctor_release(x_24, 8);
 lean_ctor_release(x_24, 9);
 lean_ctor_release(x_24, 10);
 lean_ctor_release(x_24, 11);
 lean_ctor_release(x_24, 12);
 lean_ctor_release(x_24, 13);
 lean_ctor_release(x_24, 14);
 lean_ctor_release(x_24, 15);
 lean_ctor_release(x_24, 16);
 lean_ctor_release(x_24, 17);
 lean_ctor_release(x_24, 18);
 lean_ctor_release(x_24, 19);
 lean_ctor_release(x_24, 20);
 x_167 = x_24;
} else {
 lean_dec_ref(x_24);
 x_167 = lean_box(0);
}
lean_inc(x_26);
lean_inc(x_1);
x_168 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_148, x_1, x_26);
lean_inc(x_1);
x_169 = l_Lean_PersistentArray_push___redArg(x_149, x_1);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 21, 2);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_144);
lean_ctor_set(x_170, 1, x_145);
lean_ctor_set(x_170, 2, x_146);
lean_ctor_set(x_170, 3, x_147);
lean_ctor_set(x_170, 4, x_168);
lean_ctor_set(x_170, 5, x_169);
lean_ctor_set(x_170, 6, x_150);
lean_ctor_set(x_170, 7, x_151);
lean_ctor_set(x_170, 8, x_152);
lean_ctor_set(x_170, 9, x_153);
lean_ctor_set(x_170, 10, x_154);
lean_ctor_set(x_170, 11, x_155);
lean_ctor_set(x_170, 12, x_156);
lean_ctor_set(x_170, 13, x_157);
lean_ctor_set(x_170, 14, x_158);
lean_ctor_set(x_170, 15, x_159);
lean_ctor_set(x_170, 16, x_161);
lean_ctor_set(x_170, 17, x_162);
lean_ctor_set(x_170, 18, x_163);
lean_ctor_set(x_170, 19, x_164);
lean_ctor_set(x_170, 20, x_165);
lean_ctor_set_uint8(x_170, sizeof(void*)*21, x_160);
lean_ctor_set_uint8(x_170, sizeof(void*)*21 + 1, x_166);
if (lean_is_scalar(x_143)) {
 x_171 = lean_alloc_ctor(0, 4, 0);
} else {
 x_171 = x_143;
}
lean_ctor_set(x_171, 0, x_140);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_141);
lean_ctor_set(x_171, 3, x_142);
x_172 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_172, 0, x_124);
lean_ctor_set(x_172, 1, x_125);
lean_ctor_set(x_172, 2, x_126);
lean_ctor_set(x_172, 3, x_127);
lean_ctor_set(x_172, 4, x_128);
lean_ctor_set(x_172, 5, x_129);
lean_ctor_set(x_172, 6, x_130);
lean_ctor_set(x_172, 7, x_131);
lean_ctor_set(x_172, 8, x_133);
lean_ctor_set(x_172, 9, x_134);
lean_ctor_set(x_172, 10, x_135);
lean_ctor_set(x_172, 11, x_136);
lean_ctor_set(x_172, 12, x_137);
lean_ctor_set(x_172, 13, x_138);
lean_ctor_set(x_172, 14, x_171);
lean_ctor_set(x_172, 15, x_139);
lean_ctor_set_uint8(x_172, sizeof(void*)*16, x_132);
x_173 = lean_st_ref_set(x_2, x_172, x_25);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_26);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_26);
x_179 = lean_ctor_get(x_175, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_181 = x_175;
} else {
 lean_dec_ref(x_175);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_ctor_get(x_16, 0);
lean_inc(x_183);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_183);
return x_11;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_11, 0);
x_185 = lean_ctor_get(x_11, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_11);
x_186 = lean_ctor_get(x_184, 4);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_1);
x_187 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_186, x_1);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_188 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_185);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_st_ref_take(x_2, x_190);
x_192 = lean_ctor_get(x_189, 5);
lean_inc(x_192);
lean_dec(x_189);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_193, 14);
lean_inc(x_194);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_191, 1);
lean_inc(x_196);
lean_dec(x_191);
x_197 = lean_ctor_get(x_192, 2);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_193, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_193, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 4);
lean_inc(x_202);
x_203 = lean_ctor_get(x_193, 5);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 6);
lean_inc(x_204);
x_205 = lean_ctor_get(x_193, 7);
lean_inc(x_205);
x_206 = lean_ctor_get_uint8(x_193, sizeof(void*)*16);
x_207 = lean_ctor_get(x_193, 8);
lean_inc(x_207);
x_208 = lean_ctor_get(x_193, 9);
lean_inc(x_208);
x_209 = lean_ctor_get(x_193, 10);
lean_inc(x_209);
x_210 = lean_ctor_get(x_193, 11);
lean_inc(x_210);
x_211 = lean_ctor_get(x_193, 12);
lean_inc(x_211);
x_212 = lean_ctor_get(x_193, 13);
lean_inc(x_212);
x_213 = lean_ctor_get(x_193, 15);
lean_inc(x_213);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 lean_ctor_release(x_193, 6);
 lean_ctor_release(x_193, 7);
 lean_ctor_release(x_193, 8);
 lean_ctor_release(x_193, 9);
 lean_ctor_release(x_193, 10);
 lean_ctor_release(x_193, 11);
 lean_ctor_release(x_193, 12);
 lean_ctor_release(x_193, 13);
 lean_ctor_release(x_193, 14);
 lean_ctor_release(x_193, 15);
 x_214 = x_193;
} else {
 lean_dec_ref(x_193);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_194, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_194, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_194, 3);
lean_inc(x_217);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_218 = x_194;
} else {
 lean_dec_ref(x_194);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_195, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_195, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_195, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_195, 3);
lean_inc(x_222);
x_223 = lean_ctor_get(x_195, 4);
lean_inc(x_223);
x_224 = lean_ctor_get(x_195, 5);
lean_inc(x_224);
x_225 = lean_ctor_get(x_195, 6);
lean_inc(x_225);
x_226 = lean_ctor_get(x_195, 7);
lean_inc(x_226);
x_227 = lean_ctor_get(x_195, 8);
lean_inc(x_227);
x_228 = lean_ctor_get(x_195, 9);
lean_inc(x_228);
x_229 = lean_ctor_get(x_195, 10);
lean_inc(x_229);
x_230 = lean_ctor_get(x_195, 11);
lean_inc(x_230);
x_231 = lean_ctor_get(x_195, 12);
lean_inc(x_231);
x_232 = lean_ctor_get(x_195, 13);
lean_inc(x_232);
x_233 = lean_ctor_get(x_195, 14);
lean_inc(x_233);
x_234 = lean_ctor_get(x_195, 15);
lean_inc(x_234);
x_235 = lean_ctor_get_uint8(x_195, sizeof(void*)*21);
x_236 = lean_ctor_get(x_195, 16);
lean_inc(x_236);
x_237 = lean_ctor_get(x_195, 17);
lean_inc(x_237);
x_238 = lean_ctor_get(x_195, 18);
lean_inc(x_238);
x_239 = lean_ctor_get(x_195, 19);
lean_inc(x_239);
x_240 = lean_ctor_get(x_195, 20);
lean_inc(x_240);
x_241 = lean_ctor_get_uint8(x_195, sizeof(void*)*21 + 1);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 lean_ctor_release(x_195, 5);
 lean_ctor_release(x_195, 6);
 lean_ctor_release(x_195, 7);
 lean_ctor_release(x_195, 8);
 lean_ctor_release(x_195, 9);
 lean_ctor_release(x_195, 10);
 lean_ctor_release(x_195, 11);
 lean_ctor_release(x_195, 12);
 lean_ctor_release(x_195, 13);
 lean_ctor_release(x_195, 14);
 lean_ctor_release(x_195, 15);
 lean_ctor_release(x_195, 16);
 lean_ctor_release(x_195, 17);
 lean_ctor_release(x_195, 18);
 lean_ctor_release(x_195, 19);
 lean_ctor_release(x_195, 20);
 x_242 = x_195;
} else {
 lean_dec_ref(x_195);
 x_242 = lean_box(0);
}
lean_inc(x_197);
lean_inc(x_1);
x_243 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_223, x_1, x_197);
lean_inc(x_1);
x_244 = l_Lean_PersistentArray_push___redArg(x_224, x_1);
if (lean_is_scalar(x_242)) {
 x_245 = lean_alloc_ctor(0, 21, 2);
} else {
 x_245 = x_242;
}
lean_ctor_set(x_245, 0, x_219);
lean_ctor_set(x_245, 1, x_220);
lean_ctor_set(x_245, 2, x_221);
lean_ctor_set(x_245, 3, x_222);
lean_ctor_set(x_245, 4, x_243);
lean_ctor_set(x_245, 5, x_244);
lean_ctor_set(x_245, 6, x_225);
lean_ctor_set(x_245, 7, x_226);
lean_ctor_set(x_245, 8, x_227);
lean_ctor_set(x_245, 9, x_228);
lean_ctor_set(x_245, 10, x_229);
lean_ctor_set(x_245, 11, x_230);
lean_ctor_set(x_245, 12, x_231);
lean_ctor_set(x_245, 13, x_232);
lean_ctor_set(x_245, 14, x_233);
lean_ctor_set(x_245, 15, x_234);
lean_ctor_set(x_245, 16, x_236);
lean_ctor_set(x_245, 17, x_237);
lean_ctor_set(x_245, 18, x_238);
lean_ctor_set(x_245, 19, x_239);
lean_ctor_set(x_245, 20, x_240);
lean_ctor_set_uint8(x_245, sizeof(void*)*21, x_235);
lean_ctor_set_uint8(x_245, sizeof(void*)*21 + 1, x_241);
if (lean_is_scalar(x_218)) {
 x_246 = lean_alloc_ctor(0, 4, 0);
} else {
 x_246 = x_218;
}
lean_ctor_set(x_246, 0, x_215);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_216);
lean_ctor_set(x_246, 3, x_217);
if (lean_is_scalar(x_214)) {
 x_247 = lean_alloc_ctor(0, 16, 1);
} else {
 x_247 = x_214;
}
lean_ctor_set(x_247, 0, x_198);
lean_ctor_set(x_247, 1, x_199);
lean_ctor_set(x_247, 2, x_200);
lean_ctor_set(x_247, 3, x_201);
lean_ctor_set(x_247, 4, x_202);
lean_ctor_set(x_247, 5, x_203);
lean_ctor_set(x_247, 6, x_204);
lean_ctor_set(x_247, 7, x_205);
lean_ctor_set(x_247, 8, x_207);
lean_ctor_set(x_247, 9, x_208);
lean_ctor_set(x_247, 10, x_209);
lean_ctor_set(x_247, 11, x_210);
lean_ctor_set(x_247, 12, x_211);
lean_ctor_set(x_247, 13, x_212);
lean_ctor_set(x_247, 14, x_246);
lean_ctor_set(x_247, 15, x_213);
lean_ctor_set_uint8(x_247, sizeof(void*)*16, x_206);
x_248 = lean_st_ref_set(x_2, x_247, x_196);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_197);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_197);
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_250, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_256 = x_250;
} else {
 lean_dec_ref(x_250);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_187, 0);
lean_inc(x_258);
lean_dec(x_187);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_185);
return x_259;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 5);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 5);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(x_7, x_1);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(x_1, x_2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isNatTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__3;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("var", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__6;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__9;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__12;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("div", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__15;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mod", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__18;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pow", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Int_OfNat_toExpr___closed__21;
x_2 = l_Int_OfNat_toExpr___closed__2;
x_3 = l_Int_OfNat_toExpr___closed__1;
x_4 = l_Int_OfNat_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Int_OfNat_toExpr___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_toExpr___closed__22;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Int_OfNat_toExpr___closed__5;
x_4 = l_Lean_mkNatLit(x_2);
x_5 = l_Lean_Expr_app___override(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Int_OfNat_toExpr___closed__8;
x_8 = l_Lean_mkNatLit(x_6);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Int_OfNat_toExpr___closed__11;
x_13 = l_Int_OfNat_toExpr(x_10);
x_14 = l_Int_OfNat_toExpr(x_11);
x_15 = l_Lean_mkAppB(x_12, x_13, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Int_OfNat_toExpr___closed__14;
x_19 = l_Int_OfNat_toExpr(x_16);
x_20 = l_Int_OfNat_toExpr(x_17);
x_21 = l_Lean_mkAppB(x_18, x_19, x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Int_OfNat_toExpr___closed__17;
x_25 = l_Int_OfNat_toExpr(x_22);
x_26 = l_Int_OfNat_toExpr(x_23);
x_27 = l_Lean_mkAppB(x_24, x_25, x_26);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Int_OfNat_toExpr___closed__20;
x_31 = l_Int_OfNat_toExpr(x_28);
x_32 = l_Int_OfNat_toExpr(x_29);
x_33 = l_Lean_mkAppB(x_30, x_31, x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Int_OfNat_toExpr___closed__23;
x_37 = l_Int_OfNat_toExpr(x_34);
x_38 = l_Lean_mkNatLit(x_35);
x_39 = l_Lean_mkAppB(x_36, x_37, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_instToExprExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_OfNat_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_OfNat_instToExprExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Int_OfNat_toExpr___closed__2;
x_2 = l_Int_OfNat_toExpr___closed__1;
x_3 = l_Int_OfNat_toExpr___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Int_OfNat_instToExprExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Int_OfNat_instToExprExpr___closed__0;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_instToExprExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Int_OfNat_instToExprExpr___lam__0), 1, 0);
x_2 = l_Int_OfNat_instToExprExpr___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_nat_to_int(x_3);
x_5 = l_Lean_mkIntLit(x_4);
lean_dec(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = l_outOfBounds___redArg(x_8);
x_11 = l_Lean_mkIntNatCast(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_PersistentArray_get_x21___redArg(x_8, x_1, x_6);
lean_dec(x_6);
x_13 = l_Lean_mkIntNatCast(x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_14);
x_17 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_15);
x_18 = l_Lean_mkIntAdd(x_16, x_17);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
x_21 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_19);
x_22 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_20);
x_23 = l_Lean_mkIntMul(x_21, x_22);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_26 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_24);
x_27 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_25);
x_28 = l_Lean_mkIntDiv(x_26, x_27);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
lean_inc(x_1);
x_31 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_29);
x_32 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_30);
x_33 = l_Lean_mkIntMod(x_31, x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_34);
x_37 = l_Lean_mkNatLit(x_35);
x_38 = l_Lean_mkIntPowNat(x_36, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Int_OfNat_Expr_denoteAsIntExpr_go(x_1, x_2);
x_6 = l_Lean_Meta_Grind_shareCommon___redArg(x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_1, x_2, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Int_OfNat_Expr_denoteAsIntExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__0;
x_2 = l_Int_OfNat_toExpr___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__3;
x_2 = l_Int_OfNat_toOfNatExpr___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__6;
x_2 = l_Int_OfNat_toOfNatExpr___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__9;
x_2 = l_Int_OfNat_toOfNatExpr___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__12;
x_2 = l_Int_OfNat_toOfNatExpr___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toOfNatExpr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toOfNatExpr___closed__15;
x_2 = l_Int_OfNat_toOfNatExpr___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toOfNatExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_1);
x_34 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_cleanupAnnotations(x_35);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_dec(x_37);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_36;
goto block_33;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_36;
goto block_33;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_39);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_36;
goto block_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
x_46 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_47 = l_Int_OfNat_toOfNatExpr___closed__1;
x_48 = l_Lean_Expr_isConstOf(x_46, x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isApp(x_46);
if (x_49 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_36;
goto block_33;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_51 = l_Lean_Expr_isApp(x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_36;
goto block_33;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_50);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_36;
goto block_33;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_55 = l_Int_OfNat_toOfNatExpr___closed__4;
x_56 = l_Lean_Expr_isConstOf(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Int_OfNat_toOfNatExpr___closed__7;
x_58 = l_Lean_Expr_isConstOf(x_54, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Int_OfNat_toOfNatExpr___closed__10;
x_60 = l_Lean_Expr_isConstOf(x_54, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Int_OfNat_toOfNatExpr___closed__13;
x_62 = l_Lean_Expr_isConstOf(x_54, x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Int_OfNat_toOfNatExpr___closed__16;
x_64 = l_Lean_Expr_isConstOf(x_54, x_63);
lean_dec(x_54);
if (x_64 == 0)
{
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_36;
goto block_33;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = l_Lean_Meta_isInstHAddNat___redArg(x_45, x_7, x_36);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_42);
lean_dec(x_39);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_68;
goto block_33;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_70 = l_Int_OfNat_toOfNatExpr(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_74 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_ctor_set_tag(x_70, 2);
lean_ctor_set(x_70, 1, x_76);
lean_ctor_set(x_74, 0, x_70);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
lean_ctor_set_tag(x_70, 2);
lean_ctor_set(x_70, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_70);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_free_object(x_70);
lean_dec(x_72);
return x_74;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_70, 0);
x_81 = lean_ctor_get(x_70, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_70);
x_82 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_dec(x_80);
return x_82;
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_70;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_54);
x_88 = l_Lean_Meta_isInstHMulNat___redArg(x_45, x_7, x_36);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_42);
lean_dec(x_39);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_91;
goto block_33;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_93 = l_Int_OfNat_toOfNatExpr(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
x_97 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_96);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 0);
lean_ctor_set_tag(x_93, 3);
lean_ctor_set(x_93, 1, x_99);
lean_ctor_set(x_97, 0, x_93);
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_97);
lean_ctor_set_tag(x_93, 3);
lean_ctor_set(x_93, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
lean_free_object(x_93);
lean_dec(x_95);
return x_97;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_93, 0);
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_93);
x_105 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_106);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_dec(x_103);
return x_105;
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_93;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_54);
x_111 = l_Lean_Meta_isInstHDivNat___redArg(x_45, x_7, x_36);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_42);
lean_dec(x_39);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_114;
goto block_33;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_1);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_116 = l_Int_OfNat_toOfNatExpr(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
x_120 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_119);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_120, 0);
lean_ctor_set_tag(x_116, 4);
lean_ctor_set(x_116, 1, x_122);
lean_ctor_set(x_120, 0, x_116);
return x_120;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_120);
lean_ctor_set_tag(x_116, 4);
lean_ctor_set(x_116, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_free_object(x_116);
lean_dec(x_118);
return x_120;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_116, 0);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_116);
x_128 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_129);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
else
{
lean_dec(x_126);
return x_128;
}
}
}
else
{
lean_dec(x_39);
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
}
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_54);
x_134 = l_Lean_Meta_isInstHModNat___redArg(x_45, x_7, x_36);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_42);
lean_dec(x_39);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_137;
goto block_33;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_1);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_139 = l_Int_OfNat_toOfNatExpr(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_138);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_139, 1);
x_143 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_142);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_143, 0);
lean_ctor_set_tag(x_139, 5);
lean_ctor_set(x_139, 1, x_145);
lean_ctor_set(x_143, 0, x_139);
return x_143;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_143, 0);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_143);
lean_ctor_set_tag(x_139, 5);
lean_ctor_set(x_139, 1, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_free_object(x_139);
lean_dec(x_141);
return x_143;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_139, 0);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_139);
x_151 = l_Int_OfNat_toOfNatExpr(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_155, 0, x_149);
lean_ctor_set(x_155, 1, x_152);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
else
{
lean_dec(x_149);
return x_151;
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_139;
}
}
}
}
else
{
lean_object* x_157; 
lean_dec(x_54);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_157 = l_Lean_Meta_getNatValue_x3f(x_39, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_39);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
lean_dec(x_45);
lean_dec(x_42);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_159;
goto block_33;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
lean_dec(x_158);
x_162 = l_Lean_Meta_isInstHPowNat___redArg(x_45, x_7, x_160);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_161);
lean_dec(x_42);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_165;
goto block_33;
}
else
{
uint8_t x_166; 
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_162);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_162, 1);
x_168 = lean_ctor_get(x_162, 0);
lean_dec(x_168);
x_169 = l_Int_OfNat_toOfNatExpr(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_167);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_169, 0);
lean_ctor_set_tag(x_162, 6);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 0, x_171);
lean_ctor_set(x_169, 0, x_162);
return x_169;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_169, 0);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_169);
lean_ctor_set_tag(x_162, 6);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_162);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
else
{
lean_free_object(x_162);
lean_dec(x_161);
return x_169;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_162, 1);
lean_inc(x_175);
lean_dec(x_162);
x_176 = l_Int_OfNat_toOfNatExpr(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_161);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_dec(x_161);
return x_176;
}
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_157);
if (x_182 == 0)
{
return x_157;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_157, 0);
x_184 = lean_ctor_get(x_157, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_157);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
}
}
}
else
{
lean_object* x_186; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_186 = l_Lean_Meta_getNatValue_x3f(x_1, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_11 = x_1;
x_12 = x_2;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_188;
goto block_33;
}
else
{
uint8_t x_189; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_186, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_187);
if (x_191 == 0)
{
lean_ctor_set_tag(x_187, 0);
return x_186;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_187, 0);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_186, 0, x_193);
return x_186;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_186, 1);
lean_inc(x_194);
lean_dec(x_186);
x_195 = lean_ctor_get(x_187, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 1, 0);
} else {
 x_197 = x_196;
 lean_ctor_set_tag(x_197, 0);
}
lean_ctor_set(x_197, 0, x_195);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_194);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_186);
if (x_199 == 0)
{
return x_186;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_186, 0);
x_201 = lean_ctor_get(x_186, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_186);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
}
}
block_33:
{
lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Int_OfNat_toIntLe_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntLe_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntLe_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toIntLe_x3f___closed__1;
x_2 = l_Int_OfNat_toIntLe_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntLe_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Int_OfNat_toIntLe_x3f___closed__2;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Meta_isInstLENat___redArg(x_23, x_7, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Int_OfNat_toOfNatExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Int_OfNat_toOfNatExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_40);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
return x_39;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
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
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_toIntDvd_x3f___closed__1;
x_2 = l_Int_OfNat_toIntDvd_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_toIntDvd_x3f___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_toIntDvd_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_toIntDvd_x3f___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_19 = l_Lean_Expr_cleanupAnnotations(x_1);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Int_OfNat_toIntDvd_x3f___closed__2;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Meta_isInstDvdNat___redArg(x_27, x_7, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_Lean_Meta_getNatValue_x3f(x_24, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_24);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_21);
lean_dec(x_2);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*6 + 11);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_15 = x_49;
goto block_18;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_46, 1);
x_52 = lean_ctor_get(x_46, 0);
lean_dec(x_52);
x_53 = l_Int_OfNat_toIntDvd_x3f___closed__4;
x_54 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_46, 7);
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_53);
x_55 = l_Int_OfNat_toIntDvd_x3f___closed__6;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_Grind_reportIssue(x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_15 = x_58;
goto block_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_dec(x_46);
x_60 = l_Int_OfNat_toIntDvd_x3f___closed__4;
x_61 = l_Lean_indentExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Int_OfNat_toIntDvd_x3f___closed__6;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_Grind_reportIssue(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_15 = x_66;
goto block_18;
}
}
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_1);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_dec(x_43);
x_68 = !lean_is_exclusive(x_44);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_44, 0);
x_70 = l_Int_OfNat_toOfNatExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_44, 0, x_73);
lean_ctor_set(x_70, 0, x_44);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_44, 0, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_44);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_free_object(x_44);
lean_dec(x_69);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
return x_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 0);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_44, 0);
lean_inc(x_82);
lean_dec(x_44);
x_83 = l_Int_OfNat_toOfNatExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_84);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_92 = x_83;
} else {
 lean_dec_ref(x_83);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_43);
if (x_94 == 0)
{
return x_43;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_43, 0);
x_96 = lean_ctor_get(x_43, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_43);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
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
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_toIntEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Int_OfNat_toOfNatExpr(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Int_OfNat_toOfNatExpr(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NatCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1;
x_2 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_OfNat_ofDenoteAsIntExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_89; uint8_t x_90; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_89 = l_Lean_Expr_cleanupAnnotations(x_16);
x_90 = l_Lean_Expr_isApp(x_89);
if (x_90 == 0)
{
lean_dec(x_89);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_88;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
x_92 = l_Lean_Expr_appFnCleanup___redArg(x_89);
x_93 = l_Lean_Expr_isApp(x_92);
if (x_93 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_88;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
x_95 = l_Lean_Expr_appFnCleanup___redArg(x_92);
x_96 = l_Lean_Expr_isApp(x_95);
if (x_96 == 0)
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_91);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_88;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
x_98 = l_Lean_Expr_appFnCleanup___redArg(x_95);
x_99 = l_Int_OfNat_toOfNatExpr___closed__1;
x_100 = l_Lean_Expr_isConstOf(x_98, x_99);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Expr_isApp(x_98);
if (x_101 == 0)
{
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_91);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_88;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_Expr_appFnCleanup___redArg(x_98);
x_103 = l_Lean_Expr_isApp(x_102);
if (x_103 == 0)
{
lean_dec(x_102);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_91);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_88;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_Expr_appFnCleanup___redArg(x_102);
x_105 = l_Lean_Expr_isApp(x_104);
if (x_105 == 0)
{
lean_dec(x_104);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_91);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_88;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = l_Lean_Expr_appFnCleanup___redArg(x_104);
x_107 = l_Int_OfNat_toOfNatExpr___closed__7;
x_108 = l_Lean_Expr_isConstOf(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = l_Int_OfNat_toOfNatExpr___closed__10;
x_110 = l_Lean_Expr_isConstOf(x_106, x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Int_OfNat_toOfNatExpr___closed__13;
x_112 = l_Lean_Expr_isConstOf(x_106, x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = l_Int_OfNat_toOfNatExpr___closed__16;
x_114 = l_Lean_Expr_isConstOf(x_106, x_113);
lean_dec(x_106);
if (x_114 == 0)
{
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_91);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
goto block_88;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_1);
x_115 = l_Lean_Meta_isInstHAddInt___redArg(x_97, x_7, x_17);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
uint8_t x_118; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_115, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_115, 0, x_120);
return x_115;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_dec(x_115);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
lean_dec(x_115);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_125 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_125;
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_125, 1);
x_129 = lean_ctor_get(x_125, 0);
lean_dec(x_129);
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
lean_dec(x_126);
x_131 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_dec(x_130);
lean_free_object(x_125);
return x_131;
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_132);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_132, 0);
lean_ctor_set_tag(x_125, 2);
lean_ctor_set(x_125, 1, x_136);
lean_ctor_set(x_125, 0, x_130);
lean_ctor_set(x_132, 0, x_125);
return x_131;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_132, 0);
lean_inc(x_137);
lean_dec(x_132);
lean_ctor_set_tag(x_125, 2);
lean_ctor_set(x_125, 1, x_137);
lean_ctor_set(x_125, 0, x_130);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_125);
lean_ctor_set(x_131, 0, x_138);
return x_131;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_131, 1);
lean_inc(x_139);
lean_dec(x_131);
x_140 = lean_ctor_get(x_132, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_141 = x_132;
} else {
 lean_dec_ref(x_132);
 x_141 = lean_box(0);
}
lean_ctor_set_tag(x_125, 2);
lean_ctor_set(x_125, 1, x_140);
lean_ctor_set(x_125, 0, x_130);
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
}
}
else
{
lean_dec(x_130);
lean_free_object(x_125);
return x_131;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_125, 1);
lean_inc(x_144);
lean_dec(x_125);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
lean_dec(x_126);
x_146 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_dec(x_145);
return x_146;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_151 = x_147;
} else {
 lean_dec_ref(x_147);
 x_151 = lean_box(0);
}
x_152 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_150);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_149;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_148);
return x_154;
}
}
else
{
lean_dec(x_145);
return x_146;
}
}
}
}
else
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_125;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_106);
lean_dec(x_1);
x_155 = l_Lean_Meta_isInstHMulInt___redArg(x_97, x_7, x_17);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_155, 0);
lean_dec(x_159);
x_160 = lean_box(0);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_155, 1);
lean_inc(x_161);
lean_dec(x_155);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_155, 1);
lean_inc(x_164);
lean_dec(x_155);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_165 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_165;
}
else
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_ctor_get(x_165, 0);
lean_dec(x_169);
x_170 = lean_ctor_get(x_166, 0);
lean_inc(x_170);
lean_dec(x_166);
x_171 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_dec(x_170);
lean_free_object(x_165);
return x_171;
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_171, 0);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_172);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_172, 0);
lean_ctor_set_tag(x_165, 3);
lean_ctor_set(x_165, 1, x_176);
lean_ctor_set(x_165, 0, x_170);
lean_ctor_set(x_172, 0, x_165);
return x_171;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
lean_dec(x_172);
lean_ctor_set_tag(x_165, 3);
lean_ctor_set(x_165, 1, x_177);
lean_ctor_set(x_165, 0, x_170);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_165);
lean_ctor_set(x_171, 0, x_178);
return x_171;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_171, 1);
lean_inc(x_179);
lean_dec(x_171);
x_180 = lean_ctor_get(x_172, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
lean_ctor_set_tag(x_165, 3);
lean_ctor_set(x_165, 1, x_180);
lean_ctor_set(x_165, 0, x_170);
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_165);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
return x_183;
}
}
}
else
{
lean_dec(x_170);
lean_free_object(x_165);
return x_171;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_165, 1);
lean_inc(x_184);
lean_dec(x_165);
x_185 = lean_ctor_get(x_166, 0);
lean_inc(x_185);
lean_dec(x_166);
x_186 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_184);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_dec(x_185);
return x_186;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_189 = x_186;
} else {
 lean_dec_ref(x_186);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_192, 0, x_185);
lean_ctor_set(x_192, 1, x_190);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_188);
return x_194;
}
}
else
{
lean_dec(x_185);
return x_186;
}
}
}
}
else
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_165;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_dec(x_106);
lean_dec(x_1);
x_195 = l_Lean_Meta_isInstHDivInt___redArg(x_97, x_7, x_17);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
uint8_t x_198; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_195);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_195, 0);
lean_dec(x_199);
x_200 = lean_box(0);
lean_ctor_set(x_195, 0, x_200);
return x_195;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
lean_dec(x_195);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_195, 1);
lean_inc(x_204);
lean_dec(x_195);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_205 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_205;
}
else
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_205);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_205, 1);
x_209 = lean_ctor_get(x_205, 0);
lean_dec(x_209);
x_210 = lean_ctor_get(x_206, 0);
lean_inc(x_210);
lean_dec(x_206);
x_211 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_208);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_dec(x_210);
lean_free_object(x_205);
return x_211;
}
else
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_211);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_211, 0);
lean_dec(x_214);
x_215 = !lean_is_exclusive(x_212);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_212, 0);
lean_ctor_set_tag(x_205, 4);
lean_ctor_set(x_205, 1, x_216);
lean_ctor_set(x_205, 0, x_210);
lean_ctor_set(x_212, 0, x_205);
return x_211;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_212, 0);
lean_inc(x_217);
lean_dec(x_212);
lean_ctor_set_tag(x_205, 4);
lean_ctor_set(x_205, 1, x_217);
lean_ctor_set(x_205, 0, x_210);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_205);
lean_ctor_set(x_211, 0, x_218);
return x_211;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_211, 1);
lean_inc(x_219);
lean_dec(x_211);
x_220 = lean_ctor_get(x_212, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_221 = x_212;
} else {
 lean_dec_ref(x_212);
 x_221 = lean_box(0);
}
lean_ctor_set_tag(x_205, 4);
lean_ctor_set(x_205, 1, x_220);
lean_ctor_set(x_205, 0, x_210);
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_205);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_219);
return x_223;
}
}
}
else
{
lean_dec(x_210);
lean_free_object(x_205);
return x_211;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_205, 1);
lean_inc(x_224);
lean_dec(x_205);
x_225 = lean_ctor_get(x_206, 0);
lean_inc(x_225);
lean_dec(x_206);
x_226 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_224);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_dec(x_225);
return x_226;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_227, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_231 = x_227;
} else {
 lean_dec_ref(x_227);
 x_231 = lean_box(0);
}
x_232 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_230);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_232);
if (lean_is_scalar(x_229)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_229;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_228);
return x_234;
}
}
else
{
lean_dec(x_225);
return x_226;
}
}
}
}
else
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_205;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; 
lean_dec(x_106);
lean_dec(x_1);
x_235 = l_Lean_Meta_isInstHModInt___redArg(x_97, x_7, x_17);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_unbox(x_236);
lean_dec(x_236);
if (x_237 == 0)
{
uint8_t x_238; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_238 = !lean_is_exclusive(x_235);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_235, 0);
lean_dec(x_239);
x_240 = lean_box(0);
lean_ctor_set(x_235, 0, x_240);
return x_235;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_235, 1);
lean_inc(x_241);
lean_dec(x_235);
x_242 = lean_box(0);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_235, 1);
lean_inc(x_244);
lean_dec(x_235);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_245 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_245;
}
else
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_245);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_245, 1);
x_249 = lean_ctor_get(x_245, 0);
lean_dec(x_249);
x_250 = lean_ctor_get(x_246, 0);
lean_inc(x_250);
lean_dec(x_246);
x_251 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_248);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_dec(x_250);
lean_free_object(x_245);
return x_251;
}
else
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_251);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_251, 0);
lean_dec(x_254);
x_255 = !lean_is_exclusive(x_252);
if (x_255 == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_252, 0);
lean_ctor_set_tag(x_245, 5);
lean_ctor_set(x_245, 1, x_256);
lean_ctor_set(x_245, 0, x_250);
lean_ctor_set(x_252, 0, x_245);
return x_251;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_252, 0);
lean_inc(x_257);
lean_dec(x_252);
lean_ctor_set_tag(x_245, 5);
lean_ctor_set(x_245, 1, x_257);
lean_ctor_set(x_245, 0, x_250);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_245);
lean_ctor_set(x_251, 0, x_258);
return x_251;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_ctor_get(x_251, 1);
lean_inc(x_259);
lean_dec(x_251);
x_260 = lean_ctor_get(x_252, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_261 = x_252;
} else {
 lean_dec_ref(x_252);
 x_261 = lean_box(0);
}
lean_ctor_set_tag(x_245, 5);
lean_ctor_set(x_245, 1, x_260);
lean_ctor_set(x_245, 0, x_250);
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 1, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_245);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_259);
return x_263;
}
}
}
else
{
lean_dec(x_250);
lean_free_object(x_245);
return x_251;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_245, 1);
lean_inc(x_264);
lean_dec(x_245);
x_265 = lean_ctor_get(x_246, 0);
lean_inc(x_265);
lean_dec(x_246);
x_266 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_264);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
lean_dec(x_265);
return x_266;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_267, 0);
lean_inc(x_270);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_271 = x_267;
} else {
 lean_dec_ref(x_267);
 x_271 = lean_box(0);
}
x_272 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_272, 0, x_265);
lean_ctor_set(x_272, 1, x_270);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(1, 1, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_272);
if (lean_is_scalar(x_269)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_269;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_268);
return x_274;
}
}
else
{
lean_dec(x_265);
return x_266;
}
}
}
}
else
{
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_245;
}
}
}
}
}
}
}
else
{
lean_object* x_275; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_275 = l_Lean_Meta_getIntValue_x3f(x_1, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_275);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_275, 0);
lean_dec(x_278);
x_279 = lean_box(0);
lean_ctor_set(x_275, 0, x_279);
return x_275;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_275, 1);
lean_inc(x_280);
lean_dec(x_275);
x_281 = lean_box(0);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_275);
if (x_283 == 0)
{
lean_object* x_284; uint8_t x_285; 
x_284 = lean_ctor_get(x_275, 0);
lean_dec(x_284);
x_285 = !lean_is_exclusive(x_276);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_286 = lean_ctor_get(x_276, 0);
x_287 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_288 = lean_int_dec_le(x_287, x_286);
if (x_288 == 0)
{
lean_object* x_289; 
lean_free_object(x_276);
lean_dec(x_286);
x_289 = lean_box(0);
lean_ctor_set(x_275, 0, x_289);
return x_275;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = l_Int_toNat(x_286);
lean_dec(x_286);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_276, 0, x_291);
return x_275;
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_ctor_get(x_276, 0);
lean_inc(x_292);
lean_dec(x_276);
x_293 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_294 = lean_int_dec_le(x_293, x_292);
if (x_294 == 0)
{
lean_object* x_295; 
lean_dec(x_292);
x_295 = lean_box(0);
lean_ctor_set(x_275, 0, x_295);
return x_275;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = l_Int_toNat(x_292);
lean_dec(x_292);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_275, 0, x_298);
return x_275;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_299 = lean_ctor_get(x_275, 1);
lean_inc(x_299);
lean_dec(x_275);
x_300 = lean_ctor_get(x_276, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 x_301 = x_276;
} else {
 lean_dec_ref(x_276);
 x_301 = lean_box(0);
}
x_302 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_303 = lean_int_dec_le(x_302, x_300);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_301);
lean_dec(x_300);
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_299);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = l_Int_toNat(x_300);
lean_dec(x_300);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_306);
if (lean_is_scalar(x_301)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_301;
}
lean_ctor_set(x_308, 0, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_299);
return x_309;
}
}
}
}
else
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_275);
if (x_310 == 0)
{
return x_275;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_275, 0);
x_312 = lean_ctor_get(x_275, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_275);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
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
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_88:
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_23, x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Expr_cleanupAnnotations(x_28);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_37 = l_Lean_Expr_isApp(x_36);
if (x_37 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_32);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Expr_appFnCleanup___redArg(x_36);
x_39 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_40 = l_Lean_Expr_isConstOf(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_dec(x_35);
lean_dec(x_32);
lean_free_object(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_29;
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Expr_cleanupAnnotations(x_35);
x_42 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_44 = lean_box(0);
lean_ctor_set(x_26, 0, x_44);
return x_26;
}
else
{
lean_object* x_45; 
lean_free_object(x_26);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(x_32, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_29);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
return x_45;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_45, 0);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_45);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_26, 0);
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_26);
x_61 = l_Lean_Expr_cleanupAnnotations(x_59);
x_62 = l_Lean_Expr_isApp(x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_60;
goto block_14;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = l_Lean_Expr_appFnCleanup___redArg(x_61);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_60;
goto block_14;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_68 = l_Lean_Expr_isApp(x_67);
if (x_68 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_60;
goto block_14;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_70 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_71 = l_Lean_Expr_isConstOf(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_11 = x_60;
goto block_14;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_Expr_cleanupAnnotations(x_66);
x_73 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
x_74 = l_Lean_Expr_isConstOf(x_72, x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_60);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(x_63, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_60);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_78);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_2, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_16 = lean_ctor_get(x_8, 4);
x_17 = lean_ctor_get(x_8, 5);
x_18 = lean_ctor_get(x_8, 6);
x_19 = lean_ctor_get(x_8, 7);
x_20 = lean_ctor_get(x_8, 8);
x_21 = lean_ctor_get(x_8, 9);
x_22 = lean_ctor_get(x_8, 10);
x_23 = lean_ctor_get(x_8, 11);
x_24 = lean_ctor_get(x_8, 12);
x_25 = lean_nat_dec_eq(x_15, x_16);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_27 = l_Lean_Expr_isAppOf(x_1, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Int_OfNat_toOfNatExpr___closed__1;
x_29 = l_Lean_Expr_isAppOf(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_15, x_30);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_40);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(x_2, x_45);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_41);
x_50 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_48, x_41, x_5, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_52, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_55);
lean_ctor_set_tag(x_50, 3);
lean_ctor_set(x_50, 1, x_55);
lean_ctor_set(x_50, 0, x_57);
x_58 = l_Int_Linear_Expr_norm(x_50);
lean_dec(x_50);
lean_ctor_set_tag(x_46, 5);
lean_ctor_set(x_46, 1, x_55);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_42, 1, x_46);
lean_ctor_set(x_42, 0, x_58);
x_59 = lean_grind_cutsat_assert_le(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
return x_59;
}
else
{
uint8_t x_60; 
lean_free_object(x_50);
lean_free_object(x_46);
lean_free_object(x_42);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_54);
if (x_60 == 0)
{
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_54, 0);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_54);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_50, 0);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_50);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_64, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_67);
x_70 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_71 = l_Int_Linear_Expr_norm(x_70);
lean_dec(x_70);
lean_ctor_set_tag(x_46, 5);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_42, 1, x_46);
lean_ctor_set(x_42, 0, x_71);
x_72 = lean_grind_cutsat_assert_le(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_46);
lean_free_object(x_42);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_75 = x_66;
} else {
 lean_dec_ref(x_66);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_46, 0);
x_78 = lean_ctor_get(x_46, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
lean_inc(x_41);
x_79 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_77, x_41, x_5, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_80, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_84);
if (lean_is_scalar(x_82)) {
 x_87 = lean_alloc_ctor(3, 2, 0);
} else {
 x_87 = x_82;
 lean_ctor_set_tag(x_87, 3);
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
x_88 = l_Int_Linear_Expr_norm(x_87);
lean_dec(x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_41);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_42, 1, x_89);
lean_ctor_set(x_42, 0, x_88);
x_90 = lean_grind_cutsat_assert_le(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_85);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_82);
lean_free_object(x_42);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_42, 0);
x_96 = lean_ctor_get(x_42, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_42);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(x_2, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
lean_inc(x_41);
x_101 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_98, x_41, x_5, x_99);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_102, x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_106);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(3, 2, 0);
} else {
 x_109 = x_104;
 lean_ctor_set_tag(x_109, 3);
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_106);
x_110 = l_Int_Linear_Expr_norm(x_109);
lean_dec(x_109);
if (lean_is_scalar(x_100)) {
 x_111 = lean_alloc_ctor(5, 2, 0);
} else {
 x_111 = x_100;
 lean_ctor_set_tag(x_111, 5);
}
lean_ctor_set(x_111, 0, x_41);
lean_ctor_set(x_111, 1, x_106);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_grind_cutsat_assert_le(x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_ctor_get(x_105, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_105, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_116 = x_105;
} else {
 lean_dec_ref(x_105);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_32);
if (x_118 == 0)
{
return x_32;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_32, 0);
x_120 = lean_ctor_get(x_32, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_32);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_free_object(x_8);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_10);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_free_object(x_8);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_10);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_free_object(x_8);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_17, x_10);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; 
x_127 = lean_ctor_get(x_8, 0);
x_128 = lean_ctor_get(x_8, 1);
x_129 = lean_ctor_get(x_8, 2);
x_130 = lean_ctor_get(x_8, 3);
x_131 = lean_ctor_get(x_8, 4);
x_132 = lean_ctor_get(x_8, 5);
x_133 = lean_ctor_get(x_8, 6);
x_134 = lean_ctor_get(x_8, 7);
x_135 = lean_ctor_get(x_8, 8);
x_136 = lean_ctor_get(x_8, 9);
x_137 = lean_ctor_get(x_8, 10);
x_138 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_139 = lean_ctor_get(x_8, 11);
x_140 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_141 = lean_ctor_get(x_8, 12);
lean_inc(x_141);
lean_inc(x_139);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_8);
x_142 = lean_nat_dec_eq(x_130, x_131);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_144 = l_Lean_Expr_isAppOf(x_1, x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = l_Int_OfNat_toOfNatExpr___closed__1;
x_146 = l_Lean_Expr_isAppOf(x_1, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_add(x_130, x_147);
lean_dec(x_130);
x_149 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_149, 0, x_127);
lean_ctor_set(x_149, 1, x_128);
lean_ctor_set(x_149, 2, x_129);
lean_ctor_set(x_149, 3, x_148);
lean_ctor_set(x_149, 4, x_131);
lean_ctor_set(x_149, 5, x_132);
lean_ctor_set(x_149, 6, x_133);
lean_ctor_set(x_149, 7, x_134);
lean_ctor_set(x_149, 8, x_135);
lean_ctor_set(x_149, 9, x_136);
lean_ctor_set(x_149, 10, x_137);
lean_ctor_set(x_149, 11, x_139);
lean_ctor_set(x_149, 12, x_141);
lean_ctor_set_uint8(x_149, sizeof(void*)*13, x_138);
lean_ctor_set_uint8(x_149, sizeof(void*)*13 + 1, x_140);
lean_inc(x_9);
lean_inc(x_149);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_150 = l_Int_OfNat_ofDenoteAsIntExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_149, x_9, x_10);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_box(0);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_156 = lean_ctor_get(x_150, 1);
lean_inc(x_156);
lean_dec(x_150);
x_157 = lean_ctor_get(x_151, 0);
lean_inc(x_157);
lean_dec(x_151);
x_158 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = l_Lean_Meta_Grind_Arith_Cutsat_getNatVars___redArg(x_2, x_160);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
lean_inc(x_157);
x_166 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_163, x_157, x_5, x_164);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_149);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_170 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_167, x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_149, x_9, x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0;
lean_inc(x_171);
if (lean_is_scalar(x_169)) {
 x_174 = lean_alloc_ctor(3, 2, 0);
} else {
 x_174 = x_169;
 lean_ctor_set_tag(x_174, 3);
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
x_175 = l_Int_Linear_Expr_norm(x_174);
lean_dec(x_174);
if (lean_is_scalar(x_165)) {
 x_176 = lean_alloc_ctor(5, 2, 0);
} else {
 x_176 = x_165;
 lean_ctor_set_tag(x_176, 5);
}
lean_ctor_set(x_176, 0, x_157);
lean_ctor_set(x_176, 1, x_171);
if (lean_is_scalar(x_161)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_161;
}
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_grind_cutsat_assert_le(x_177, x_2, x_3, x_4, x_5, x_6, x_7, x_149, x_9, x_172);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_169);
lean_dec(x_165);
lean_dec(x_161);
lean_dec(x_157);
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = lean_ctor_get(x_170, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_ctor_get(x_150, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_150, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_185 = x_150;
} else {
 lean_dec_ref(x_150);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_10);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_10);
return x_190;
}
}
else
{
lean_object* x_191; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg(x_132, x_10);
return x_191;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_cleanupAnnotations(x_1);
x_17 = l_Lean_Expr_isApp(x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2;
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = x_11;
goto block_15;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_cleanupAnnotations(x_21);
x_28 = l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_11);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Int_OfNat_toOfNatExpr___closed__1;
x_33 = l_Lean_Expr_isAppOf(x_18, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_3, x_11);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_36, 6);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(x_38, x_18);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_34);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1;
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
lean_inc(x_2);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_2);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_grind_cutsat_assert_le(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_box(0);
lean_ctor_set(x_34, 0, x_55);
return x_34;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_34, 0);
x_57 = lean_ctor_get(x_34, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_34);
x_58 = lean_ctor_get(x_56, 6);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_alreadyInternalized_spec__0___redArg(x_58, x_18);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1;
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2;
lean_inc(x_2);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_2);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_2);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_grind_cutsat_assert_le(x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_73 = x_60;
} else {
 lean_dec_ref(x_60);
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
lean_object* x_75; lean_object* x_76; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_57);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_11);
return x_78;
}
}
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_OfNat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_OfNat_toExpr___closed__0 = _init_l_Int_OfNat_toExpr___closed__0();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__0);
l_Int_OfNat_toExpr___closed__1 = _init_l_Int_OfNat_toExpr___closed__1();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__1);
l_Int_OfNat_toExpr___closed__2 = _init_l_Int_OfNat_toExpr___closed__2();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__2);
l_Int_OfNat_toExpr___closed__3 = _init_l_Int_OfNat_toExpr___closed__3();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__3);
l_Int_OfNat_toExpr___closed__4 = _init_l_Int_OfNat_toExpr___closed__4();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__4);
l_Int_OfNat_toExpr___closed__5 = _init_l_Int_OfNat_toExpr___closed__5();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__5);
l_Int_OfNat_toExpr___closed__6 = _init_l_Int_OfNat_toExpr___closed__6();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__6);
l_Int_OfNat_toExpr___closed__7 = _init_l_Int_OfNat_toExpr___closed__7();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__7);
l_Int_OfNat_toExpr___closed__8 = _init_l_Int_OfNat_toExpr___closed__8();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__8);
l_Int_OfNat_toExpr___closed__9 = _init_l_Int_OfNat_toExpr___closed__9();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__9);
l_Int_OfNat_toExpr___closed__10 = _init_l_Int_OfNat_toExpr___closed__10();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__10);
l_Int_OfNat_toExpr___closed__11 = _init_l_Int_OfNat_toExpr___closed__11();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__11);
l_Int_OfNat_toExpr___closed__12 = _init_l_Int_OfNat_toExpr___closed__12();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__12);
l_Int_OfNat_toExpr___closed__13 = _init_l_Int_OfNat_toExpr___closed__13();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__13);
l_Int_OfNat_toExpr___closed__14 = _init_l_Int_OfNat_toExpr___closed__14();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__14);
l_Int_OfNat_toExpr___closed__15 = _init_l_Int_OfNat_toExpr___closed__15();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__15);
l_Int_OfNat_toExpr___closed__16 = _init_l_Int_OfNat_toExpr___closed__16();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__16);
l_Int_OfNat_toExpr___closed__17 = _init_l_Int_OfNat_toExpr___closed__17();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__17);
l_Int_OfNat_toExpr___closed__18 = _init_l_Int_OfNat_toExpr___closed__18();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__18);
l_Int_OfNat_toExpr___closed__19 = _init_l_Int_OfNat_toExpr___closed__19();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__19);
l_Int_OfNat_toExpr___closed__20 = _init_l_Int_OfNat_toExpr___closed__20();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__20);
l_Int_OfNat_toExpr___closed__21 = _init_l_Int_OfNat_toExpr___closed__21();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__21);
l_Int_OfNat_toExpr___closed__22 = _init_l_Int_OfNat_toExpr___closed__22();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__22);
l_Int_OfNat_toExpr___closed__23 = _init_l_Int_OfNat_toExpr___closed__23();
lean_mark_persistent(l_Int_OfNat_toExpr___closed__23);
l_Int_OfNat_instToExprExpr___closed__0 = _init_l_Int_OfNat_instToExprExpr___closed__0();
lean_mark_persistent(l_Int_OfNat_instToExprExpr___closed__0);
l_Int_OfNat_instToExprExpr___closed__1 = _init_l_Int_OfNat_instToExprExpr___closed__1();
lean_mark_persistent(l_Int_OfNat_instToExprExpr___closed__1);
l_Int_OfNat_instToExprExpr = _init_l_Int_OfNat_instToExprExpr();
lean_mark_persistent(l_Int_OfNat_instToExprExpr);
l_Int_OfNat_toOfNatExpr___closed__0 = _init_l_Int_OfNat_toOfNatExpr___closed__0();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__0);
l_Int_OfNat_toOfNatExpr___closed__1 = _init_l_Int_OfNat_toOfNatExpr___closed__1();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__1);
l_Int_OfNat_toOfNatExpr___closed__2 = _init_l_Int_OfNat_toOfNatExpr___closed__2();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__2);
l_Int_OfNat_toOfNatExpr___closed__3 = _init_l_Int_OfNat_toOfNatExpr___closed__3();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__3);
l_Int_OfNat_toOfNatExpr___closed__4 = _init_l_Int_OfNat_toOfNatExpr___closed__4();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__4);
l_Int_OfNat_toOfNatExpr___closed__5 = _init_l_Int_OfNat_toOfNatExpr___closed__5();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__5);
l_Int_OfNat_toOfNatExpr___closed__6 = _init_l_Int_OfNat_toOfNatExpr___closed__6();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__6);
l_Int_OfNat_toOfNatExpr___closed__7 = _init_l_Int_OfNat_toOfNatExpr___closed__7();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__7);
l_Int_OfNat_toOfNatExpr___closed__8 = _init_l_Int_OfNat_toOfNatExpr___closed__8();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__8);
l_Int_OfNat_toOfNatExpr___closed__9 = _init_l_Int_OfNat_toOfNatExpr___closed__9();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__9);
l_Int_OfNat_toOfNatExpr___closed__10 = _init_l_Int_OfNat_toOfNatExpr___closed__10();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__10);
l_Int_OfNat_toOfNatExpr___closed__11 = _init_l_Int_OfNat_toOfNatExpr___closed__11();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__11);
l_Int_OfNat_toOfNatExpr___closed__12 = _init_l_Int_OfNat_toOfNatExpr___closed__12();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__12);
l_Int_OfNat_toOfNatExpr___closed__13 = _init_l_Int_OfNat_toOfNatExpr___closed__13();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__13);
l_Int_OfNat_toOfNatExpr___closed__14 = _init_l_Int_OfNat_toOfNatExpr___closed__14();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__14);
l_Int_OfNat_toOfNatExpr___closed__15 = _init_l_Int_OfNat_toOfNatExpr___closed__15();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__15);
l_Int_OfNat_toOfNatExpr___closed__16 = _init_l_Int_OfNat_toOfNatExpr___closed__16();
lean_mark_persistent(l_Int_OfNat_toOfNatExpr___closed__16);
l_Int_OfNat_toIntLe_x3f___closed__0 = _init_l_Int_OfNat_toIntLe_x3f___closed__0();
lean_mark_persistent(l_Int_OfNat_toIntLe_x3f___closed__0);
l_Int_OfNat_toIntLe_x3f___closed__1 = _init_l_Int_OfNat_toIntLe_x3f___closed__1();
lean_mark_persistent(l_Int_OfNat_toIntLe_x3f___closed__1);
l_Int_OfNat_toIntLe_x3f___closed__2 = _init_l_Int_OfNat_toIntLe_x3f___closed__2();
lean_mark_persistent(l_Int_OfNat_toIntLe_x3f___closed__2);
l_Int_OfNat_toIntDvd_x3f___closed__0 = _init_l_Int_OfNat_toIntDvd_x3f___closed__0();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__0);
l_Int_OfNat_toIntDvd_x3f___closed__1 = _init_l_Int_OfNat_toIntDvd_x3f___closed__1();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__1);
l_Int_OfNat_toIntDvd_x3f___closed__2 = _init_l_Int_OfNat_toIntDvd_x3f___closed__2();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__2);
l_Int_OfNat_toIntDvd_x3f___closed__3 = _init_l_Int_OfNat_toIntDvd_x3f___closed__3();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__3);
l_Int_OfNat_toIntDvd_x3f___closed__4 = _init_l_Int_OfNat_toIntDvd_x3f___closed__4();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__4);
l_Int_OfNat_toIntDvd_x3f___closed__5 = _init_l_Int_OfNat_toIntDvd_x3f___closed__5();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__5);
l_Int_OfNat_toIntDvd_x3f___closed__6 = _init_l_Int_OfNat_toIntDvd_x3f___closed__6();
lean_mark_persistent(l_Int_OfNat_toIntDvd_x3f___closed__6);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__0);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__1);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__2);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__3);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__4);
l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5 = _init_l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5();
lean_mark_persistent(l_Int_OfNat_ofDenoteAsIntExpr_x3f___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0___redArg___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
