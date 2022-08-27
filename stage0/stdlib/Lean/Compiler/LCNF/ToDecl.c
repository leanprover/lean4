// Lean compiler output
// Module: Lean.Compiler.LCNF.ToDecl
// Imports: Init Lean.Meta.Transform Lean.Meta.Match.MatcherInfo Lean.Compiler.LCNF.ToLCNF
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__23;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__21;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_LCNF_inlineMatchers___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__6;
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__8;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_macroInline___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__5;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__4;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__14;
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_LCNF_inlineMatchers___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__15;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__22;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__5;
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__7;
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__24;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* lean_is_unsafe_rec_name(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_TSyntax_getNat___spec__1(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__3;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__5;
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__19;
static lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__1;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__12;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(x_1, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Core_instantiateValueLevelParams(x_9, x_2, x_5, x_6, x_10);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_14);
x_16 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_17, x_19);
x_21 = l_Lean_Expr_beta(x_13, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_25);
x_27 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_28, x_30);
x_32 = l_Lean_Expr_beta(x_23, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 2;
lean_inc(x_6);
x_14 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_12, x_13, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_8);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_macroInline___lambda__1(x_6, x_7, x_1, x_16, x_2, x_3, x_11);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 2;
lean_inc(x_6);
x_22 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_20, x_21, x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Compiler_LCNF_macroInline___lambda__1(x_6, x_7, x_1, x_25, x_2, x_3, x_19);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_macroInline___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_macroInline___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lambda__3___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Compiler_LCNF_macroInline___closed__1;
x_6 = l_Lean_Compiler_LCNF_macroInline___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_macroInline___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_macroInline___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_3);
x_10 = l_Array_append___rarg(x_1, x_3);
x_11 = l_Lean_mkAppN(x_2, x_3);
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_10, x_11, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_7 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___closed__1;
lean_inc(x_1);
x_8 = lean_array_push(x_7, x_1);
x_9 = 0;
x_10 = 1;
x_11 = 1;
x_12 = l_Lean_Meta_mkLambdaFVars(x_8, x_1, x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_k", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_eq(x_10, x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_1, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_13 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_nat_sub(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1___boxed), 9, 2);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_2);
x_19 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(x_14, x_17, x_18, x_5, x_6, x_7, x_8, x_15);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_2);
x_24 = lean_array_get_size(x_3);
lean_inc(x_1);
lean_inc(x_3);
x_25 = l_Array_toSubarray___rarg(x_3, x_1, x_24);
x_26 = l_Array_ofSubarray___rarg(x_25);
x_27 = 0;
x_28 = 1;
x_29 = 1;
x_30 = l_Lean_Meta_mkLambdaFVars(x_26, x_4, x_27, x_28, x_29, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2;
x_34 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_33, x_7, x_8, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_37 = lean_infer_type(x_31, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(x_35, x_38, x_31, x_40, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_toSubarray___rarg(x_3, x_44, x_1);
x_46 = l_Array_ofSubarray___rarg(x_45);
x_47 = l_Lean_Meta_mkLambdaFVars(x_46, x_42, x_27, x_28, x_29, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_30);
if (x_56 == 0)
{
return x_30;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_30, 0);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_30);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_9);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3), 9, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
lean_dec(x_1);
lean_inc(x_10);
x_18 = lean_array_set(x_2, x_3, x_10);
lean_dec(x_3);
x_19 = lean_array_push(x_4, x_10);
x_20 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_5, x_6, x_7, x_8, x_9, x_17, x_18, x_19, x_11, x_12, x_13, x_14, x_15);
return x_20;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_alt", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_6, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
x_18 = l_Lean_Core_instantiateValueLevelParams(x_16, x_2, x_11, x_12, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_beta(x_19, x_7);
x_22 = 0;
x_23 = 1;
x_24 = 1;
x_25 = l_Lean_Meta_mkLambdaFVars(x_8, x_21, x_22, x_23, x_24, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_56; lean_object* x_57; lean_object* x_80; uint8_t x_81; lean_object* x_82; uint8_t x_83; 
x_30 = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(x_3);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_30);
x_80 = lean_array_get_size(x_5);
x_81 = lean_nat_dec_lt(x_6, x_80);
lean_dec(x_80);
x_82 = lean_array_get_size(x_7);
x_83 = lean_nat_dec_lt(x_31, x_82);
lean_dec(x_82);
if (x_81 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__4;
x_85 = l_panic___at_Lean_TSyntax_getNat___spec__1(x_84);
if (x_83 == 0)
{
x_32 = x_85;
goto block_55;
}
else
{
x_56 = x_85;
x_57 = lean_box(0);
goto block_79;
}
}
else
{
lean_object* x_86; 
x_86 = lean_array_fget(x_5, x_6);
if (x_83 == 0)
{
x_32 = x_86;
goto block_55;
}
else
{
x_56 = x_86;
x_57 = lean_box(0);
goto block_79;
}
}
block_55:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__4;
x_34 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_33);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_35 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(x_34, x_32, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__6;
x_39 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_38, x_11, x_12, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_36);
x_42 = lean_infer_type(x_36, x_9, x_10, x_11, x_12, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1), 15, 9);
lean_closure_set(x_45, 0, x_6);
lean_closure_set(x_45, 1, x_7);
lean_closure_set(x_45, 2, x_31);
lean_closure_set(x_45, 3, x_8);
lean_closure_set(x_45, 4, x_1);
lean_closure_set(x_45, 5, x_2);
lean_closure_set(x_45, 6, x_3);
lean_closure_set(x_45, 7, x_4);
lean_closure_set(x_45, 8, x_5);
x_46 = l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(x_40, x_43, x_36, x_45, x_9, x_10, x_11, x_12, x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
block_79:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_array_fget(x_7, x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_59 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(x_58, x_56, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__6;
x_63 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_62, x_11, x_12, x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_60);
x_66 = lean_infer_type(x_60, x_9, x_10, x_11, x_12, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1), 15, 9);
lean_closure_set(x_69, 0, x_6);
lean_closure_set(x_69, 1, x_7);
lean_closure_set(x_69, 2, x_31);
lean_closure_set(x_69, 3, x_8);
lean_closure_set(x_69, 4, x_1);
lean_closure_set(x_69, 5, x_2);
lean_closure_set(x_69, 6, x_3);
lean_closure_set(x_69, 7, x_4);
lean_closure_set(x_69, 8, x_5);
x_70 = l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(x_64, x_67, x_60, x_69, x_9, x_10, x_11, x_12, x_68);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_66);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_59);
if (x_75 == 0)
{
return x_59;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_59, 0);
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_59);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_LCNF_inlineMatchers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_10, x_1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
lean_inc(x_2);
x_9 = l_Lean_mkAppN(x_1, x_2);
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_2, x_9, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_LCNF_inlineMatchers___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_23);
x_25 = l_Lean_Meta_Match_MatcherInfo_arity(x_22);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
uint8_t x_27; 
lean_free_object(x_10);
x_27 = lean_nat_dec_lt(x_24, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
lean_free_object(x_11);
x_28 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_24);
x_29 = lean_mk_array(x_24, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_24, x_30);
lean_dec(x_24);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_29, x_31);
x_33 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_22);
x_34 = lean_ctor_get(x_22, 2);
lean_inc(x_34);
x_35 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_36 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_22, x_33, x_34, x_23, x_32, x_35, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_36, 0);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_36);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_nat_sub(x_25, x_24);
lean_dec(x_24);
lean_dec(x_25);
lean_ctor_set(x_11, 0, x_51);
x_52 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed), 8, 1);
lean_closure_set(x_52, 0, x_1);
x_53 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(x_49, x_11, x_52, x_2, x_3, x_4, x_5, x_50);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_11);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_ctor_set(x_10, 0, x_58);
return x_10;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_60);
x_62 = l_Lean_Meta_Match_MatcherInfo_arity(x_59);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
uint8_t x_64; 
lean_free_object(x_10);
x_64 = lean_nat_dec_lt(x_61, x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_62);
x_65 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_61);
x_66 = lean_mk_array(x_61, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_61, x_67);
lean_dec(x_61);
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_66, x_68);
x_70 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_59);
x_71 = lean_ctor_get(x_59, 2);
lean_inc(x_71);
x_72 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_73 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_59, x_70, x_71, x_60, x_69, x_72, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_74);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_73, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
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
else
{
lean_object* x_83; 
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_83 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_nat_sub(x_62, x_61);
lean_dec(x_61);
lean_dec(x_62);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed), 8, 1);
lean_closure_set(x_88, 0, x_1);
x_89 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(x_84, x_87, x_88, x_2, x_3, x_4, x_5, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_94; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_ctor_set(x_10, 0, x_94);
return x_10;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_95 = lean_ctor_get(x_10, 1);
lean_inc(x_95);
lean_dec(x_10);
x_96 = lean_ctor_get(x_11, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_97 = x_11;
} else {
 lean_dec_ref(x_11);
 x_97 = lean_box(0);
}
x_98 = lean_unsigned_to_nat(0u);
x_99 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_98);
x_100 = l_Lean_Meta_Match_MatcherInfo_arity(x_96);
x_101 = lean_nat_dec_lt(x_100, x_99);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_nat_dec_lt(x_99, x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_100);
lean_dec(x_97);
x_103 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_99);
x_104 = lean_mk_array(x_99, x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_99, x_105);
lean_dec(x_99);
x_107 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_104, x_106);
x_108 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_96);
x_109 = lean_ctor_get(x_96, 2);
lean_inc(x_109);
x_110 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_111 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_96, x_108, x_109, x_98, x_107, x_110, x_2, x_3, x_4, x_5, x_95);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_112);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_119 = x_111;
} else {
 lean_dec_ref(x_111);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; 
lean_dec(x_96);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_121 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_95);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_nat_sub(x_100, x_99);
lean_dec(x_99);
lean_dec(x_100);
if (lean_is_scalar(x_97)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_97;
}
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed), 8, 1);
lean_closure_set(x_126, 0, x_1);
x_127 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(x_122, x_125, x_126, x_2, x_3, x_4, x_5, x_123);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_121, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_121, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_130 = x_121;
} else {
 lean_dec_ref(x_121);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_95);
return x_133;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_6);
return x_135;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_3);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_3);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__5;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__8;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__11;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__12;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__14;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__16;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__17;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__20;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__21;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__3___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_inlineMatchers___closed__22;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_inlineMatchers___closed__23;
x_12 = l_Lean_Compiler_LCNF_inlineMatchers___closed__24;
x_13 = 0;
x_14 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_3);
lean_inc(x_9);
x_15 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_11, x_12, x_13, x_14, x_9, x_2, x_3, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_3, x_17);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_9, x_19);
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_LCNF_inlineMatchers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Compiler_LCNF_inlineMatchers___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_is_unsafe_rec_name(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Expr_const___override(x_10, x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_6 = l_Lean_Compiler_LCNF_macroInline___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_2, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_14);
x_16 = lean_ctor_get(x_3, 2);
x_17 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_16);
x_19 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
lean_inc(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23);
x_25 = lean_ctor_get(x_3, 2);
x_26 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
lean_inc(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
lean_inc(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_etaExpand(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkLambdaFVars(x_1, x_9, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration `", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` not found", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` does not have a value", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lambda__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_unsafe_rec", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_119 = l_Lean_Compiler_LCNF_toDecl___closed__8;
lean_inc(x_1);
x_120 = l_Lean_Name_str___override(x_1, x_119);
lean_inc(x_9);
x_121 = lean_environment_find(x_9, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
lean_inc(x_1);
x_122 = lean_environment_find(x_9, x_1);
x_10 = x_122;
goto block_118;
}
else
{
uint8_t x_123; 
lean_dec(x_9);
x_123 = !lean_is_exclusive(x_121);
if (x_123 == 0)
{
x_10 = x_121;
goto block_118;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_10 = x_125;
goto block_118;
}
}
block_118:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Compiler_LCNF_toDecl___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Compiler_LCNF_toDecl___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_15, x_2, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_ConstantInfo_value_x3f(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = l_Lean_Compiler_LCNF_toDecl___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Compiler_LCNF_toDecl___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_23, x_2, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lean_ConstantInfo_type(x_17);
x_27 = lean_st_ref_get(x_4, x_8);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_inlineMatchers___closed__22;
x_30 = lean_st_mk_ref(x_29, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_31);
x_34 = l_Lean_Compiler_LCNF_toLCNFType(x_26, x_33, x_31, x_3, x_4, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Compiler_LCNF_toDecl___closed__7;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_31);
x_38 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_25, x_37, x_33, x_31, x_3, x_4, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_42 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_4);
lean_inc(x_3);
x_43 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_39, x_41, x_42, x_3, x_4, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_47 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_44, x_46, x_42, x_3, x_4, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_4);
lean_inc(x_3);
x_50 = l_Lean_Compiler_LCNF_inlineMatchers(x_48, x_3, x_4, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_4, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_31, x_54);
lean_dec(x_31);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_51, x_2, x_3, x_4, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 1)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 5)
{
uint8_t x_60; 
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec(x_58);
x_63 = l_Lean_ConstantInfo_levelParams(x_17);
lean_dec(x_17);
x_64 = lean_ctor_get(x_62, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 4);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_66, 2, x_35);
lean_ctor_set(x_66, 3, x_64);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_57, 0, x_66);
return x_57;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_dec(x_57);
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
lean_dec(x_58);
x_69 = l_Lean_ConstantInfo_levelParams(x_17);
lean_dec(x_17);
x_70 = lean_ctor_get(x_68, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 4);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_35);
lean_ctor_set(x_72, 3, x_70);
lean_ctor_set(x_72, 4, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_59);
x_74 = !lean_is_exclusive(x_57);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_57, 0);
lean_dec(x_75);
x_76 = l_Lean_ConstantInfo_levelParams(x_17);
lean_dec(x_17);
x_77 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 2, x_35);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_58);
lean_ctor_set(x_57, 0, x_78);
return x_57;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
lean_dec(x_57);
x_80 = l_Lean_ConstantInfo_levelParams(x_17);
lean_dec(x_17);
x_81 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_35);
lean_ctor_set(x_82, 3, x_81);
lean_ctor_set(x_82, 4, x_58);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_57);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_57, 0);
lean_dec(x_85);
x_86 = l_Lean_ConstantInfo_levelParams(x_17);
lean_dec(x_17);
x_87 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_88 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_87);
lean_ctor_set(x_88, 4, x_58);
lean_ctor_set(x_57, 0, x_88);
return x_57;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_57, 1);
lean_inc(x_89);
lean_dec(x_57);
x_90 = l_Lean_ConstantInfo_levelParams(x_17);
lean_dec(x_17);
x_91 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_35);
lean_ctor_set(x_92, 3, x_91);
lean_ctor_set(x_92, 4, x_58);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_57);
if (x_94 == 0)
{
return x_57;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_57, 0);
x_96 = lean_ctor_get(x_57, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_57);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_50);
if (x_98 == 0)
{
return x_50;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_50, 0);
x_100 = lean_ctor_get(x_50, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_50);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_47);
if (x_102 == 0)
{
return x_47;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_47, 0);
x_104 = lean_ctor_get(x_47, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_47);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_43);
if (x_106 == 0)
{
return x_43;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_43, 0);
x_108 = lean_ctor_get(x_43, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_43);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_38);
if (x_110 == 0)
{
return x_38;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_38, 0);
x_112 = lean_ctor_get(x_38, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_38);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_34);
if (x_114 == 0)
{
return x_34;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_34, 0);
x_116 = lean_ctor_get(x_34, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_34);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToLCNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1);
l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1);
l_Lean_Compiler_LCNF_macroInline___closed__1 = _init_l_Lean_Compiler_LCNF_macroInline___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_macroInline___closed__1);
l_Lean_Compiler_LCNF_macroInline___closed__2 = _init_l_Lean_Compiler_LCNF_macroInline___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_macroInline___closed__2);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___closed__1 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___closed__1);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__3 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__3);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__4 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__4);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__5 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__5);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__6 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__6);
l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1);
l_Lean_Compiler_LCNF_inlineMatchers___closed__1 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__1);
l_Lean_Compiler_LCNF_inlineMatchers___closed__2 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__2);
l_Lean_Compiler_LCNF_inlineMatchers___closed__3 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__3);
l_Lean_Compiler_LCNF_inlineMatchers___closed__4 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__4);
l_Lean_Compiler_LCNF_inlineMatchers___closed__5 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__5);
l_Lean_Compiler_LCNF_inlineMatchers___closed__6 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__6);
l_Lean_Compiler_LCNF_inlineMatchers___closed__7 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__7);
l_Lean_Compiler_LCNF_inlineMatchers___closed__8 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__8);
l_Lean_Compiler_LCNF_inlineMatchers___closed__9 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__9);
l_Lean_Compiler_LCNF_inlineMatchers___closed__10 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__10);
l_Lean_Compiler_LCNF_inlineMatchers___closed__11 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__11);
l_Lean_Compiler_LCNF_inlineMatchers___closed__12 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__12);
l_Lean_Compiler_LCNF_inlineMatchers___closed__13 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__13);
l_Lean_Compiler_LCNF_inlineMatchers___closed__14 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__14);
l_Lean_Compiler_LCNF_inlineMatchers___closed__15 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__15);
l_Lean_Compiler_LCNF_inlineMatchers___closed__16 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__16);
l_Lean_Compiler_LCNF_inlineMatchers___closed__17 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__17);
l_Lean_Compiler_LCNF_inlineMatchers___closed__18 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__18);
l_Lean_Compiler_LCNF_inlineMatchers___closed__19 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__19);
l_Lean_Compiler_LCNF_inlineMatchers___closed__20 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__20);
l_Lean_Compiler_LCNF_inlineMatchers___closed__21 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__21);
l_Lean_Compiler_LCNF_inlineMatchers___closed__22 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__22);
l_Lean_Compiler_LCNF_inlineMatchers___closed__23 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__23);
l_Lean_Compiler_LCNF_inlineMatchers___closed__24 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__24);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1);
l_Lean_Compiler_LCNF_toDecl___closed__1 = _init_l_Lean_Compiler_LCNF_toDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__1);
l_Lean_Compiler_LCNF_toDecl___closed__2 = _init_l_Lean_Compiler_LCNF_toDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__2);
l_Lean_Compiler_LCNF_toDecl___closed__3 = _init_l_Lean_Compiler_LCNF_toDecl___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__3);
l_Lean_Compiler_LCNF_toDecl___closed__4 = _init_l_Lean_Compiler_LCNF_toDecl___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__4);
l_Lean_Compiler_LCNF_toDecl___closed__5 = _init_l_Lean_Compiler_LCNF_toDecl___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__5);
l_Lean_Compiler_LCNF_toDecl___closed__6 = _init_l_Lean_Compiler_LCNF_toDecl___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__6);
l_Lean_Compiler_LCNF_toDecl___closed__7 = _init_l_Lean_Compiler_LCNF_toDecl___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__7);
l_Lean_Compiler_LCNF_toDecl___closed__8 = _init_l_Lean_Compiler_LCNF_toDecl___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
