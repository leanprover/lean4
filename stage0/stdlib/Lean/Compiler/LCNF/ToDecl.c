// Lean compiler output
// Module: Lean.Compiler.LCNF.ToDecl
// Imports: Lean.Meta.Transform Lean.Meta.Match.MatcherInfo Lean.Compiler.ExternAttr Lean.Compiler.InitAttr Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.ToLCNF
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__8;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
extern lean_object* l_Lean_instInhabitedExternAttrData;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_inlineAttrs;
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2;
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__15;
extern uint8_t l_Lean_Compiler_instInhabitedInlineAttributeKind;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_marked_borrowed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__14;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
static lean_object* l_Lean_Compiler_LCNF_macroInline___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__5;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnumAttributes_getValue___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
static lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1;
lean_object* lean_is_unsafe_rec_name(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__3;
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__7;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__8;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__9;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_externAttr;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__11;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
static uint64_t l_Lean_Compiler_LCNF_inlineMatchers___closed__2;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__6;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Core_instantiateValueLevelParams(x_9, x_2, x_5, x_6, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
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
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
x_14 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_12, x_13, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
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
x_22 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(x_20, x_21, x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
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
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lambda__2___boxed), 4, 0);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_macroInline___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = 0;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_10, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = l_Array_append___rarg(x_1, x_3);
x_11 = l_Lean_mkAppN(x_2, x_3);
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_10, x_11, x_12, x_13, x_12, x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_array_mk(x_8);
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_9, x_1, x_10, x_11, x_10, x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_9);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_k", 2, 2);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
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
x_19 = 0;
x_20 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_14, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_15);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_2);
x_25 = lean_array_get_size(x_3);
lean_inc(x_1);
lean_inc(x_3);
x_26 = l_Array_toSubarray___rarg(x_3, x_1, x_25);
x_27 = l_Array_ofSubarray___rarg(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = 1;
x_30 = 1;
x_31 = l_Lean_Meta_mkLambdaFVars(x_27, x_4, x_28, x_29, x_28, x_30, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__2;
x_35 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_34, x_7, x_8, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_32);
x_38 = lean_infer_type(x_32, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3;
x_42 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(x_36, x_39, x_32, x_41, x_42, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_toSubarray___rarg(x_3, x_46, x_1);
x_48 = l_Array_ofSubarray___rarg(x_47);
lean_dec(x_47);
x_49 = l_Lean_Meta_mkLambdaFVars(x_48, x_44, x_28, x_29, x_28, x_30, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_48);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_31);
if (x_58 == 0)
{
return x_31;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_31, 0);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_31);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_9);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3), 9, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = 0;
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_1, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_inc(x_8);
x_16 = lean_array_set(x_2, x_3, x_8);
x_17 = lean_array_push(x_4, x_8);
x_18 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_alt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_3);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Core_instantiateValueLevelParams(x_16, x_2, x_9, x_10, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_beta(x_19, x_5);
x_22 = 0;
x_23 = 1;
x_24 = 1;
x_25 = l_Lean_Meta_mkLambdaFVars(x_6, x_21, x_22, x_23, x_22, x_24, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(x_3);
x_35 = lean_nat_add(x_4, x_34);
lean_dec(x_34);
x_36 = lean_array_fget(x_13, x_4);
lean_dec(x_13);
x_37 = l_Lean_instInhabitedExpr;
x_38 = lean_array_get(x_37, x_5, x_35);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(x_38, x_36, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__2;
x_43 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_42, x_9, x_10, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_40);
x_46 = lean_infer_type(x_40, x_7, x_8, x_9, x_10, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1___boxed), 13, 7);
lean_closure_set(x_49, 0, x_4);
lean_closure_set(x_49, 1, x_5);
lean_closure_set(x_49, 2, x_35);
lean_closure_set(x_49, 3, x_6);
lean_closure_set(x_49, 4, x_1);
lean_closure_set(x_49, 5, x_2);
lean_closure_set(x_49, 6, x_3);
x_50 = 0;
x_51 = l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1___rarg(x_44, x_47, x_40, x_49, x_50, x_7, x_8, x_9, x_10, x_48);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_35);
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
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 0);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_46);
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
lean_dec(x_35);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = l_Lean_mkAppN(x_1, x_2);
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_2, x_9, x_10, x_11, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
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
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
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
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
lean_free_object(x_11);
x_28 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_24);
x_29 = lean_mk_array(x_24, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_24, x_30);
lean_dec(x_24);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_29, x_31);
x_33 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_34 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_22, x_23, x_32, x_33, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_46 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_nat_sub(x_25, x_24);
lean_dec(x_24);
lean_dec(x_25);
lean_ctor_set(x_11, 0, x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed), 8, 1);
lean_closure_set(x_50, 0, x_1);
x_51 = 0;
x_52 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_47, x_11, x_50, x_51, x_2, x_3, x_4, x_5, x_48);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; 
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
x_57 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_ctor_set(x_10, 0, x_57);
return x_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
lean_dec(x_11);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_59);
x_61 = l_Lean_Meta_Match_MatcherInfo_arity(x_58);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
uint8_t x_63; 
lean_free_object(x_10);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
x_64 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_60);
x_65 = lean_mk_array(x_60, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_60, x_66);
lean_dec(x_60);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_65, x_67);
x_69 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_70 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_58, x_59, x_68, x_69, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_80 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_nat_sub(x_61, x_60);
lean_dec(x_60);
lean_dec(x_61);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed), 8, 1);
lean_closure_set(x_85, 0, x_1);
x_86 = 0;
x_87 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_81, x_84, x_85, x_86, x_2, x_3, x_4, x_5, x_82);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_ctor_get(x_80, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_90 = x_80;
} else {
 lean_dec_ref(x_80);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
lean_ctor_set(x_10, 0, x_92);
return x_10;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_ctor_get(x_10, 1);
lean_inc(x_93);
lean_dec(x_10);
x_94 = lean_ctor_get(x_11, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_95 = x_11;
} else {
 lean_dec_ref(x_11);
 x_95 = lean_box(0);
}
x_96 = lean_unsigned_to_nat(0u);
x_97 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_96);
x_98 = l_Lean_Meta_Match_MatcherInfo_arity(x_94);
x_99 = lean_nat_dec_lt(x_98, x_97);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = lean_nat_dec_lt(x_97, x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_98);
lean_dec(x_95);
x_101 = l_Lean_Compiler_LCNF_macroInline___lambda__1___closed__1;
lean_inc(x_97);
x_102 = lean_mk_array(x_97, x_101);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_sub(x_97, x_103);
lean_dec(x_97);
x_105 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_102, x_104);
x_106 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_107 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_94, x_96, x_105, x_106, x_2, x_3, x_4, x_5, x_93);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_108);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_115 = x_107;
} else {
 lean_dec_ref(x_107);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_94);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_117 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_93);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_nat_sub(x_98, x_97);
lean_dec(x_97);
lean_dec(x_98);
if (lean_is_scalar(x_95)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_95;
}
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__1___boxed), 8, 1);
lean_closure_set(x_122, 0, x_1);
x_123 = 0;
x_124 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_118, x_121, x_122, x_123, x_2, x_3, x_4, x_5, x_119);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_ctor_get(x_117, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_127 = x_117;
} else {
 lean_dec_ref(x_117);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_93);
return x_130;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_6);
return x_132;
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
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_2);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
lean_ctor_set_uint8(x_6, 17, x_2);
return x_6;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__2;
x_5 = 0;
x_6 = l_Lean_Compiler_LCNF_inlineMatchers___closed__8;
x_7 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_2);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 10, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__11;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__15() {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Compiler_LCNF_inlineMatchers___closed__14;
x_10 = l_Lean_Compiler_LCNF_inlineMatchers___closed__15;
x_11 = 0;
x_12 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_7);
x_13 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_9, x_10, x_11, x_11, x_12, x_7, x_2, x_3, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_7, x_15);
lean_dec(x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
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
lean_dec(x_2);
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
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = l_Lean_Expr_const___override(x_11, x_6);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Expr_const___override(x_14, x_6);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_macroInline___lambda__2___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_unsafe_rec", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Name_str___override(x_1, x_9);
x_11 = 0;
lean_inc(x_8);
x_12 = l_Lean_Environment_find_x3f(x_8, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Environment_find_x3f(x_8, x_1, x_11);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1;
lean_inc(x_1);
x_21 = l_Lean_Name_str___override(x_1, x_20);
x_22 = 0;
lean_inc(x_19);
x_23 = l_Lean_Environment_find_x3f(x_19, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Environment_find_x3f(x_19, x_1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_getDeclInfo_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_4, 2);
x_19 = l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_20);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_28);
lean_inc(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_3, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_4, 2);
x_41 = l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_40);
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
lean_inc(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_37;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
lean_dec(x_14);
lean_inc(x_17);
x_19 = lean_is_marked_borrowed(x_17);
x_20 = l_Lean_Compiler_LCNF_mkParam(x_16, x_17, x_19, x_2, x_3, x_4, x_5, x_6);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_array_push(x_15, x_22);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_7 = x_25;
x_8 = x_23;
goto block_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_array_push(x_15, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_7 = x_30;
x_8 = x_27;
goto block_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_7 = x_33;
x_8 = x_6;
goto block_13;
}
block_13:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_1 = x_11;
x_6 = x_8;
goto _start;
}
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
x_14 = l_Lean_Meta_mkLambdaFVars(x_1, x_9, x_11, x_12, x_11, x_13, x_3, x_4, x_5, x_6, x_10);
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
x_1 = lean_mk_string_unchecked("declaration `", 13, 13);
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
x_1 = lean_mk_string_unchecked("` not found", 11, 11);
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
x_1 = l_Lean_Compiler_inlineAttrs;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_externAttr;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` does not have a value", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_etaExpand), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__11;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_is_unsafe_rec_name(x_1);
if (lean_obj_tag(x_7) == 0)
{
x_8 = x_1;
goto block_743;
}
else
{
lean_object* x_744; 
lean_dec(x_1);
x_744 = lean_ctor_get(x_7, 0);
lean_inc(x_744);
lean_dec(x_7);
x_8 = x_744;
goto block_743;
}
block_743:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_getDeclInfo_x3f(x_8, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_MessageData_ofName(x_8);
x_15 = l_Lean_Compiler_LCNF_toDecl___closed__2;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_14);
lean_ctor_set(x_9, 0, x_15);
x_16 = l_Lean_Compiler_LCNF_toDecl___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_17, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_MessageData_ofName(x_8);
x_21 = l_Lean_Compiler_LCNF_toDecl___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Compiler_LCNF_toDecl___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_24, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_738; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_738 = l_Lean_ConstantInfo_isPartial(x_27);
if (x_738 == 0)
{
uint8_t x_739; 
x_739 = l_Lean_ConstantInfo_isUnsafe(x_27);
if (x_739 == 0)
{
uint8_t x_740; 
x_740 = 1;
x_28 = x_740;
goto block_737;
}
else
{
uint8_t x_741; 
x_741 = 0;
x_28 = x_741;
goto block_737;
}
}
else
{
uint8_t x_742; 
x_742 = 0;
x_28 = x_742;
goto block_737;
}
block_737:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_st_ref_get(x_5, x_26);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_instInhabitedInlineAttributeKind;
x_35 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_36 = lean_box(x_34);
lean_inc(x_8);
x_37 = l_Lean_EnumAttributes_getValue___rarg(x_36, x_35, x_33, x_8);
x_38 = lean_st_ref_get(x_5, x_32);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_instInhabitedExternAttrData;
x_44 = l_Lean_Compiler_LCNF_toDecl___closed__6;
lean_inc(x_8);
lean_inc(x_42);
x_45 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_43, x_44, x_42, x_8);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_inc(x_8);
x_46 = l_Lean_hasInitAttr(x_42, x_8);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; 
x_47 = 1;
lean_inc(x_27);
x_48 = l_Lean_ConstantInfo_value_x3f(x_27, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
lean_dec(x_27);
x_49 = l_Lean_MessageData_ofName(x_8);
x_50 = l_Lean_Compiler_LCNF_toDecl___closed__2;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_49);
lean_ctor_set(x_38, 0, x_50);
x_51 = l_Lean_Compiler_LCNF_toDecl___closed__8;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_51);
lean_ctor_set(x_29, 0, x_38);
x_52 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_29, x_2, x_3, x_4, x_5, x_41);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
else
{
uint8_t x_53; 
lean_free_object(x_38);
lean_free_object(x_29);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = l_Lean_ConstantInfo_type(x_27);
x_56 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_57 = lean_st_mk_ref(x_56, x_41);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_58);
x_61 = l_Lean_Compiler_LCNF_toLCNFType(x_55, x_60, x_58, x_4, x_5, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_65 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_58);
x_66 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_54, x_64, x_65, x_60, x_58, x_4, x_5, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_70 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_71 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_67, x_69, x_70, x_4, x_5, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_75 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_72, x_74, x_70, x_4, x_5, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_5);
lean_inc(x_4);
x_78 = l_Lean_Compiler_LCNF_inlineMatchers(x_76, x_4, x_5, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_5);
lean_inc(x_4);
x_81 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_79, x_74, x_70, x_4, x_5, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_58, x_83);
lean_dec(x_58);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_82, x_2, x_3, x_4, x_5, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_87) == 1)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
switch (lean_obj_tag(x_90)) {
case 4:
{
uint8_t x_91; 
lean_free_object(x_48);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 0, x_87);
x_94 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_95 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_62);
lean_ctor_set(x_95, 3, x_94);
lean_ctor_set(x_95, 4, x_90);
lean_ctor_set(x_95, 5, x_37);
lean_ctor_set_uint8(x_95, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_95, sizeof(void*)*6 + 1, x_28);
x_96 = lean_apply_6(x_89, x_95, x_2, x_3, x_4, x_5, x_88);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_90);
x_97 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_87);
x_99 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_100 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_100, 0, x_8);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set(x_100, 2, x_62);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_100, 4, x_98);
lean_ctor_set(x_100, 5, x_37);
lean_ctor_set_uint8(x_100, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_100, sizeof(void*)*6 + 1, x_28);
x_101 = lean_apply_6(x_89, x_100, x_2, x_3, x_4, x_5, x_88);
return x_101;
}
}
case 5:
{
uint8_t x_102; 
lean_free_object(x_48);
x_102 = !lean_is_exclusive(x_90);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_90, 0);
lean_dec(x_103);
x_104 = lean_ctor_get(x_87, 0);
lean_inc(x_104);
lean_dec(x_87);
x_105 = l_Lean_Compiler_LCNF_eraseFunDecl(x_104, x_65, x_2, x_3, x_4, x_5, x_88);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_108 = lean_ctor_get(x_104, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 4);
lean_inc(x_109);
lean_dec(x_104);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 0, x_109);
x_110 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_110, 0, x_8);
lean_ctor_set(x_110, 1, x_107);
lean_ctor_set(x_110, 2, x_62);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_90);
lean_ctor_set(x_110, 5, x_37);
lean_ctor_set_uint8(x_110, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_110, sizeof(void*)*6 + 1, x_28);
x_111 = lean_apply_6(x_89, x_110, x_2, x_3, x_4, x_5, x_106);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_90);
x_112 = lean_ctor_get(x_87, 0);
lean_inc(x_112);
lean_dec(x_87);
x_113 = l_Lean_Compiler_LCNF_eraseFunDecl(x_112, x_65, x_2, x_3, x_4, x_5, x_88);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_116 = lean_ctor_get(x_112, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 4);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_119, 0, x_8);
lean_ctor_set(x_119, 1, x_115);
lean_ctor_set(x_119, 2, x_62);
lean_ctor_set(x_119, 3, x_116);
lean_ctor_set(x_119, 4, x_118);
lean_ctor_set(x_119, 5, x_37);
lean_ctor_set_uint8(x_119, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_119, sizeof(void*)*6 + 1, x_28);
x_120 = lean_apply_6(x_89, x_119, x_2, x_3, x_4, x_5, x_114);
return x_120;
}
}
case 6:
{
uint8_t x_121; 
lean_free_object(x_48);
x_121 = !lean_is_exclusive(x_90);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_90, 0);
lean_dec(x_122);
x_123 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_90, 0);
lean_ctor_set(x_90, 0, x_87);
x_124 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_125 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_125, 0, x_8);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_62);
lean_ctor_set(x_125, 3, x_124);
lean_ctor_set(x_125, 4, x_90);
lean_ctor_set(x_125, 5, x_37);
lean_ctor_set_uint8(x_125, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_125, sizeof(void*)*6 + 1, x_28);
x_126 = lean_apply_6(x_89, x_125, x_2, x_3, x_4, x_5, x_88);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_90);
x_127 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_87);
x_129 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_130 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_130, 0, x_8);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_62);
lean_ctor_set(x_130, 3, x_129);
lean_ctor_set(x_130, 4, x_128);
lean_ctor_set(x_130, 5, x_37);
lean_ctor_set_uint8(x_130, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_130, sizeof(void*)*6 + 1, x_28);
x_131 = lean_apply_6(x_89, x_130, x_2, x_3, x_4, x_5, x_88);
return x_131;
}
}
default: 
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_90);
x_132 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_87);
x_133 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_134 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_134, 0, x_8);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 2, x_62);
lean_ctor_set(x_134, 3, x_133);
lean_ctor_set(x_134, 4, x_48);
lean_ctor_set(x_134, 5, x_37);
lean_ctor_set_uint8(x_134, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_134, sizeof(void*)*6 + 1, x_28);
x_135 = lean_apply_6(x_89, x_134, x_2, x_3, x_4, x_5, x_88);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_87);
x_137 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_138 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_138, 0, x_8);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 2, x_62);
lean_ctor_set(x_138, 3, x_137);
lean_ctor_set(x_138, 4, x_48);
lean_ctor_set(x_138, 5, x_37);
lean_ctor_set_uint8(x_138, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_138, sizeof(void*)*6 + 1, x_28);
x_139 = lean_apply_6(x_89, x_138, x_2, x_3, x_4, x_5, x_88);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_62);
lean_free_object(x_48);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = !lean_is_exclusive(x_86);
if (x_140 == 0)
{
return x_86;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_86, 0);
x_142 = lean_ctor_get(x_86, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_86);
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
lean_dec(x_62);
lean_dec(x_58);
lean_free_object(x_48);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_81);
if (x_144 == 0)
{
return x_81;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_81, 0);
x_146 = lean_ctor_get(x_81, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_81);
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
lean_dec(x_62);
lean_dec(x_58);
lean_free_object(x_48);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_78);
if (x_148 == 0)
{
return x_78;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_78, 0);
x_150 = lean_ctor_get(x_78, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_78);
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
lean_dec(x_62);
lean_dec(x_58);
lean_free_object(x_48);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_75);
if (x_152 == 0)
{
return x_75;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_75, 0);
x_154 = lean_ctor_get(x_75, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_75);
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
lean_dec(x_62);
lean_dec(x_58);
lean_free_object(x_48);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_71);
if (x_156 == 0)
{
return x_71;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_71, 0);
x_158 = lean_ctor_get(x_71, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_71);
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
lean_dec(x_62);
lean_dec(x_58);
lean_free_object(x_48);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_66);
if (x_160 == 0)
{
return x_66;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_66, 0);
x_162 = lean_ctor_get(x_66, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_66);
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
lean_dec(x_58);
lean_free_object(x_48);
lean_dec(x_54);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_61);
if (x_164 == 0)
{
return x_61;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_61, 0);
x_166 = lean_ctor_get(x_61, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_61);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_168 = lean_ctor_get(x_48, 0);
lean_inc(x_168);
lean_dec(x_48);
x_169 = l_Lean_ConstantInfo_type(x_27);
x_170 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_171 = lean_st_mk_ref(x_170, x_41);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_172);
x_175 = l_Lean_Compiler_LCNF_toLCNFType(x_169, x_174, x_172, x_4, x_5, x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_179 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_172);
x_180 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_168, x_178, x_179, x_174, x_172, x_4, x_5, x_177);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_184 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_185 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_181, x_183, x_184, x_4, x_5, x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_189 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_186, x_188, x_184, x_4, x_5, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_5);
lean_inc(x_4);
x_192 = l_Lean_Compiler_LCNF_inlineMatchers(x_190, x_4, x_5, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_5);
lean_inc(x_4);
x_195 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_193, x_188, x_184, x_4, x_5, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_st_ref_get(x_172, x_197);
lean_dec(x_172);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_200 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_196, x_2, x_3, x_4, x_5, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_201) == 1)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
switch (lean_obj_tag(x_204)) {
case 4:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_205 = x_204;
} else {
 lean_dec_ref(x_204);
 x_205 = lean_box(0);
}
x_206 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 1, 0);
} else {
 x_207 = x_205;
 lean_ctor_set_tag(x_207, 0);
}
lean_ctor_set(x_207, 0, x_201);
x_208 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_209 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_209, 0, x_8);
lean_ctor_set(x_209, 1, x_206);
lean_ctor_set(x_209, 2, x_176);
lean_ctor_set(x_209, 3, x_208);
lean_ctor_set(x_209, 4, x_207);
lean_ctor_set(x_209, 5, x_37);
lean_ctor_set_uint8(x_209, sizeof(void*)*6, x_179);
lean_ctor_set_uint8(x_209, sizeof(void*)*6 + 1, x_28);
x_210 = lean_apply_6(x_203, x_209, x_2, x_3, x_4, x_5, x_202);
return x_210;
}
case 5:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_211 = x_204;
} else {
 lean_dec_ref(x_204);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_201, 0);
lean_inc(x_212);
lean_dec(x_201);
x_213 = l_Lean_Compiler_LCNF_eraseFunDecl(x_212, x_179, x_2, x_3, x_4, x_5, x_202);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_216 = lean_ctor_get(x_212, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 4);
lean_inc(x_217);
lean_dec(x_212);
if (lean_is_scalar(x_211)) {
 x_218 = lean_alloc_ctor(0, 1, 0);
} else {
 x_218 = x_211;
 lean_ctor_set_tag(x_218, 0);
}
lean_ctor_set(x_218, 0, x_217);
x_219 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_219, 0, x_8);
lean_ctor_set(x_219, 1, x_215);
lean_ctor_set(x_219, 2, x_176);
lean_ctor_set(x_219, 3, x_216);
lean_ctor_set(x_219, 4, x_218);
lean_ctor_set(x_219, 5, x_37);
lean_ctor_set_uint8(x_219, sizeof(void*)*6, x_179);
lean_ctor_set_uint8(x_219, sizeof(void*)*6 + 1, x_28);
x_220 = lean_apply_6(x_203, x_219, x_2, x_3, x_4, x_5, x_214);
return x_220;
}
case 6:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_221 = x_204;
} else {
 lean_dec_ref(x_204);
 x_221 = lean_box(0);
}
x_222 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(0, 1, 0);
} else {
 x_223 = x_221;
 lean_ctor_set_tag(x_223, 0);
}
lean_ctor_set(x_223, 0, x_201);
x_224 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_225 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_225, 0, x_8);
lean_ctor_set(x_225, 1, x_222);
lean_ctor_set(x_225, 2, x_176);
lean_ctor_set(x_225, 3, x_224);
lean_ctor_set(x_225, 4, x_223);
lean_ctor_set(x_225, 5, x_37);
lean_ctor_set_uint8(x_225, sizeof(void*)*6, x_179);
lean_ctor_set_uint8(x_225, sizeof(void*)*6 + 1, x_28);
x_226 = lean_apply_6(x_203, x_225, x_2, x_3, x_4, x_5, x_202);
return x_226;
}
default: 
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_204);
x_227 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_228 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_228, 0, x_201);
x_229 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_230 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_230, 0, x_8);
lean_ctor_set(x_230, 1, x_227);
lean_ctor_set(x_230, 2, x_176);
lean_ctor_set(x_230, 3, x_229);
lean_ctor_set(x_230, 4, x_228);
lean_ctor_set(x_230, 5, x_37);
lean_ctor_set_uint8(x_230, sizeof(void*)*6, x_179);
lean_ctor_set_uint8(x_230, sizeof(void*)*6 + 1, x_28);
x_231 = lean_apply_6(x_203, x_230, x_2, x_3, x_4, x_5, x_202);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_201);
x_234 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_235 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_235, 0, x_8);
lean_ctor_set(x_235, 1, x_232);
lean_ctor_set(x_235, 2, x_176);
lean_ctor_set(x_235, 3, x_234);
lean_ctor_set(x_235, 4, x_233);
lean_ctor_set(x_235, 5, x_37);
lean_ctor_set_uint8(x_235, sizeof(void*)*6, x_179);
lean_ctor_set_uint8(x_235, sizeof(void*)*6 + 1, x_28);
x_236 = lean_apply_6(x_203, x_235, x_2, x_3, x_4, x_5, x_202);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_176);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_237 = lean_ctor_get(x_200, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_200, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_239 = x_200;
} else {
 lean_dec_ref(x_200);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_176);
lean_dec(x_172);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_241 = lean_ctor_get(x_195, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_195, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_243 = x_195;
} else {
 lean_dec_ref(x_195);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_176);
lean_dec(x_172);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_245 = lean_ctor_get(x_192, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_192, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_247 = x_192;
} else {
 lean_dec_ref(x_192);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_176);
lean_dec(x_172);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_249 = lean_ctor_get(x_189, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_189, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_251 = x_189;
} else {
 lean_dec_ref(x_189);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_176);
lean_dec(x_172);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_253 = lean_ctor_get(x_185, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_185, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_255 = x_185;
} else {
 lean_dec_ref(x_185);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_176);
lean_dec(x_172);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_257 = lean_ctor_get(x_180, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_180, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_259 = x_180;
} else {
 lean_dec_ref(x_180);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_172);
lean_dec(x_168);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_261 = lean_ctor_get(x_175, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_175, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_263 = x_175;
} else {
 lean_dec_ref(x_175);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_free_object(x_38);
lean_free_object(x_29);
x_265 = l_Lean_ConstantInfo_type(x_27);
x_266 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_267 = lean_st_mk_ref(x_266, x_41);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_268);
x_271 = l_Lean_Compiler_LCNF_toLCNFType(x_265, x_270, x_268, x_4, x_5, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_st_ref_get(x_268, x_273);
lean_dec(x_268);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_276 = lean_ctor_get(x_274, 1);
x_277 = lean_ctor_get(x_274, 0);
lean_dec(x_277);
x_278 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_272);
lean_ctor_set(x_274, 1, x_278);
lean_ctor_set(x_274, 0, x_272);
x_279 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_274, x_2, x_3, x_4, x_5, x_276);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; 
x_281 = lean_ctor_get(x_279, 0);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_283 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_284 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_285 = 0;
x_286 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_286, 0, x_8);
lean_ctor_set(x_286, 1, x_283);
lean_ctor_set(x_286, 2, x_272);
lean_ctor_set(x_286, 3, x_282);
lean_ctor_set(x_286, 4, x_284);
lean_ctor_set(x_286, 5, x_37);
lean_ctor_set_uint8(x_286, sizeof(void*)*6, x_285);
lean_ctor_set_uint8(x_286, sizeof(void*)*6 + 1, x_28);
lean_ctor_set(x_279, 0, x_286);
return x_279;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; 
x_287 = lean_ctor_get(x_279, 0);
x_288 = lean_ctor_get(x_279, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_279);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_291 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_292 = 0;
x_293 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_293, 0, x_8);
lean_ctor_set(x_293, 1, x_290);
lean_ctor_set(x_293, 2, x_272);
lean_ctor_set(x_293, 3, x_289);
lean_ctor_set(x_293, 4, x_291);
lean_ctor_set(x_293, 5, x_37);
lean_ctor_set_uint8(x_293, sizeof(void*)*6, x_292);
lean_ctor_set_uint8(x_293, sizeof(void*)*6 + 1, x_28);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_288);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; 
x_295 = lean_ctor_get(x_274, 1);
lean_inc(x_295);
lean_dec(x_274);
x_296 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_272);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_272);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_297, x_2, x_3, x_4, x_5, x_295);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_303 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_304 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_305 = 0;
x_306 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_306, 0, x_8);
lean_ctor_set(x_306, 1, x_303);
lean_ctor_set(x_306, 2, x_272);
lean_ctor_set(x_306, 3, x_302);
lean_ctor_set(x_306, 4, x_304);
lean_ctor_set(x_306, 5, x_37);
lean_ctor_set_uint8(x_306, sizeof(void*)*6, x_305);
lean_ctor_set_uint8(x_306, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_301)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_301;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_300);
return x_307;
}
}
else
{
uint8_t x_308; 
lean_dec(x_268);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_308 = !lean_is_exclusive(x_271);
if (x_308 == 0)
{
return x_271;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_271, 0);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_271);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_42);
lean_free_object(x_38);
lean_free_object(x_29);
x_312 = !lean_is_exclusive(x_45);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_313 = lean_ctor_get(x_45, 0);
x_314 = l_Lean_ConstantInfo_type(x_27);
x_315 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_316 = lean_st_mk_ref(x_315, x_41);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_317);
x_320 = l_Lean_Compiler_LCNF_toLCNFType(x_314, x_319, x_317, x_4, x_5, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_st_ref_get(x_317, x_322);
lean_dec(x_317);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_325 = lean_ctor_get(x_323, 1);
x_326 = lean_ctor_get(x_323, 0);
lean_dec(x_326);
x_327 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_321);
lean_ctor_set(x_323, 1, x_327);
lean_ctor_set(x_323, 0, x_321);
x_328 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_323, x_2, x_3, x_4, x_5, x_325);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_330 = lean_ctor_get(x_328, 0);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_332 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_333 = 0;
x_334 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_334, 0, x_8);
lean_ctor_set(x_334, 1, x_332);
lean_ctor_set(x_334, 2, x_321);
lean_ctor_set(x_334, 3, x_331);
lean_ctor_set(x_334, 4, x_45);
lean_ctor_set(x_334, 5, x_37);
lean_ctor_set_uint8(x_334, sizeof(void*)*6, x_333);
lean_ctor_set_uint8(x_334, sizeof(void*)*6 + 1, x_28);
lean_ctor_set(x_328, 0, x_334);
return x_328;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; 
x_335 = lean_ctor_get(x_328, 0);
x_336 = lean_ctor_get(x_328, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_328);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_339 = 0;
x_340 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_340, 0, x_8);
lean_ctor_set(x_340, 1, x_338);
lean_ctor_set(x_340, 2, x_321);
lean_ctor_set(x_340, 3, x_337);
lean_ctor_set(x_340, 4, x_45);
lean_ctor_set(x_340, 5, x_37);
lean_ctor_set_uint8(x_340, sizeof(void*)*6, x_339);
lean_ctor_set_uint8(x_340, sizeof(void*)*6 + 1, x_28);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_336);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
x_342 = lean_ctor_get(x_323, 1);
lean_inc(x_342);
lean_dec(x_323);
x_343 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_321);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_321);
lean_ctor_set(x_344, 1, x_343);
x_345 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_344, x_2, x_3, x_4, x_5, x_342);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
x_350 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_351 = 0;
x_352 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_352, 0, x_8);
lean_ctor_set(x_352, 1, x_350);
lean_ctor_set(x_352, 2, x_321);
lean_ctor_set(x_352, 3, x_349);
lean_ctor_set(x_352, 4, x_45);
lean_ctor_set(x_352, 5, x_37);
lean_ctor_set_uint8(x_352, sizeof(void*)*6, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_348)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_348;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_347);
return x_353;
}
}
else
{
uint8_t x_354; 
lean_dec(x_317);
lean_free_object(x_45);
lean_dec(x_313);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_354 = !lean_is_exclusive(x_320);
if (x_354 == 0)
{
return x_320;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_320, 0);
x_356 = lean_ctor_get(x_320, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_320);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_358 = lean_ctor_get(x_45, 0);
lean_inc(x_358);
lean_dec(x_45);
x_359 = l_Lean_ConstantInfo_type(x_27);
x_360 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_361 = lean_st_mk_ref(x_360, x_41);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_362);
x_365 = l_Lean_Compiler_LCNF_toLCNFType(x_359, x_364, x_362, x_4, x_5, x_363);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = lean_st_ref_get(x_362, x_367);
lean_dec(x_362);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_370 = x_368;
} else {
 lean_dec_ref(x_368);
 x_370 = lean_box(0);
}
x_371 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_366);
if (lean_is_scalar(x_370)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_370;
}
lean_ctor_set(x_372, 0, x_366);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_372, x_2, x_3, x_4, x_5, x_369);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_374, 1);
lean_inc(x_377);
lean_dec(x_374);
x_378 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_358);
x_380 = 0;
x_381 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_381, 0, x_8);
lean_ctor_set(x_381, 1, x_378);
lean_ctor_set(x_381, 2, x_366);
lean_ctor_set(x_381, 3, x_377);
lean_ctor_set(x_381, 4, x_379);
lean_ctor_set(x_381, 5, x_37);
lean_ctor_set_uint8(x_381, sizeof(void*)*6, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_376)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_376;
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_375);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_362);
lean_dec(x_358);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_383 = lean_ctor_get(x_365, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_365, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_385 = x_365;
} else {
 lean_dec_ref(x_365);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
}
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_387 = lean_ctor_get(x_38, 0);
x_388 = lean_ctor_get(x_38, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_38);
x_389 = lean_ctor_get(x_387, 0);
lean_inc(x_389);
lean_dec(x_387);
x_390 = l_Lean_instInhabitedExternAttrData;
x_391 = l_Lean_Compiler_LCNF_toDecl___closed__6;
lean_inc(x_8);
lean_inc(x_389);
x_392 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_390, x_391, x_389, x_8);
if (lean_obj_tag(x_392) == 0)
{
uint8_t x_393; 
lean_inc(x_8);
x_393 = l_Lean_hasInitAttr(x_389, x_8);
if (x_393 == 0)
{
uint8_t x_394; lean_object* x_395; 
x_394 = 1;
lean_inc(x_27);
x_395 = l_Lean_ConstantInfo_value_x3f(x_27, x_394);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_37);
lean_dec(x_27);
x_396 = l_Lean_MessageData_ofName(x_8);
x_397 = l_Lean_Compiler_LCNF_toDecl___closed__2;
x_398 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_396);
x_399 = l_Lean_Compiler_LCNF_toDecl___closed__8;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_399);
lean_ctor_set(x_29, 0, x_398);
x_400 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_29, x_2, x_3, x_4, x_5, x_388);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_free_object(x_29);
x_401 = lean_ctor_get(x_395, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 x_402 = x_395;
} else {
 lean_dec_ref(x_395);
 x_402 = lean_box(0);
}
x_403 = l_Lean_ConstantInfo_type(x_27);
x_404 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_405 = lean_st_mk_ref(x_404, x_388);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_406);
x_409 = l_Lean_Compiler_LCNF_toLCNFType(x_403, x_408, x_406, x_4, x_5, x_407);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_413 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_406);
x_414 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_401, x_412, x_413, x_408, x_406, x_4, x_5, x_411);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_418 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_419 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_415, x_417, x_418, x_4, x_5, x_416);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_423 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_420, x_422, x_418, x_4, x_5, x_421);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
lean_inc(x_5);
lean_inc(x_4);
x_426 = l_Lean_Compiler_LCNF_inlineMatchers(x_424, x_4, x_5, x_425);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
lean_inc(x_5);
lean_inc(x_4);
x_429 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_427, x_422, x_418, x_4, x_5, x_428);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_st_ref_get(x_406, x_431);
lean_dec(x_406);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_434 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_430, x_2, x_3, x_4, x_5, x_433);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_437 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_435) == 1)
{
lean_object* x_438; 
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
switch (lean_obj_tag(x_438)) {
case 4:
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_402);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_439 = x_438;
} else {
 lean_dec_ref(x_438);
 x_439 = lean_box(0);
}
x_440 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 1, 0);
} else {
 x_441 = x_439;
 lean_ctor_set_tag(x_441, 0);
}
lean_ctor_set(x_441, 0, x_435);
x_442 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_443 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_443, 0, x_8);
lean_ctor_set(x_443, 1, x_440);
lean_ctor_set(x_443, 2, x_410);
lean_ctor_set(x_443, 3, x_442);
lean_ctor_set(x_443, 4, x_441);
lean_ctor_set(x_443, 5, x_37);
lean_ctor_set_uint8(x_443, sizeof(void*)*6, x_413);
lean_ctor_set_uint8(x_443, sizeof(void*)*6 + 1, x_28);
x_444 = lean_apply_6(x_437, x_443, x_2, x_3, x_4, x_5, x_436);
return x_444;
}
case 5:
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_402);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_445 = x_438;
} else {
 lean_dec_ref(x_438);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_435, 0);
lean_inc(x_446);
lean_dec(x_435);
x_447 = l_Lean_Compiler_LCNF_eraseFunDecl(x_446, x_413, x_2, x_3, x_4, x_5, x_436);
x_448 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
lean_dec(x_447);
x_449 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_450 = lean_ctor_get(x_446, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_446, 4);
lean_inc(x_451);
lean_dec(x_446);
if (lean_is_scalar(x_445)) {
 x_452 = lean_alloc_ctor(0, 1, 0);
} else {
 x_452 = x_445;
 lean_ctor_set_tag(x_452, 0);
}
lean_ctor_set(x_452, 0, x_451);
x_453 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_453, 0, x_8);
lean_ctor_set(x_453, 1, x_449);
lean_ctor_set(x_453, 2, x_410);
lean_ctor_set(x_453, 3, x_450);
lean_ctor_set(x_453, 4, x_452);
lean_ctor_set(x_453, 5, x_37);
lean_ctor_set_uint8(x_453, sizeof(void*)*6, x_413);
lean_ctor_set_uint8(x_453, sizeof(void*)*6 + 1, x_28);
x_454 = lean_apply_6(x_437, x_453, x_2, x_3, x_4, x_5, x_448);
return x_454;
}
case 6:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_402);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_455 = x_438;
} else {
 lean_dec_ref(x_438);
 x_455 = lean_box(0);
}
x_456 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_455)) {
 x_457 = lean_alloc_ctor(0, 1, 0);
} else {
 x_457 = x_455;
 lean_ctor_set_tag(x_457, 0);
}
lean_ctor_set(x_457, 0, x_435);
x_458 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_459 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_459, 0, x_8);
lean_ctor_set(x_459, 1, x_456);
lean_ctor_set(x_459, 2, x_410);
lean_ctor_set(x_459, 3, x_458);
lean_ctor_set(x_459, 4, x_457);
lean_ctor_set(x_459, 5, x_37);
lean_ctor_set_uint8(x_459, sizeof(void*)*6, x_413);
lean_ctor_set_uint8(x_459, sizeof(void*)*6 + 1, x_28);
x_460 = lean_apply_6(x_437, x_459, x_2, x_3, x_4, x_5, x_436);
return x_460;
}
default: 
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_438);
x_461 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_402)) {
 x_462 = lean_alloc_ctor(0, 1, 0);
} else {
 x_462 = x_402;
 lean_ctor_set_tag(x_462, 0);
}
lean_ctor_set(x_462, 0, x_435);
x_463 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_464 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_464, 0, x_8);
lean_ctor_set(x_464, 1, x_461);
lean_ctor_set(x_464, 2, x_410);
lean_ctor_set(x_464, 3, x_463);
lean_ctor_set(x_464, 4, x_462);
lean_ctor_set(x_464, 5, x_37);
lean_ctor_set_uint8(x_464, sizeof(void*)*6, x_413);
lean_ctor_set_uint8(x_464, sizeof(void*)*6 + 1, x_28);
x_465 = lean_apply_6(x_437, x_464, x_2, x_3, x_4, x_5, x_436);
return x_465;
}
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_402)) {
 x_467 = lean_alloc_ctor(0, 1, 0);
} else {
 x_467 = x_402;
 lean_ctor_set_tag(x_467, 0);
}
lean_ctor_set(x_467, 0, x_435);
x_468 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_469 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_469, 0, x_8);
lean_ctor_set(x_469, 1, x_466);
lean_ctor_set(x_469, 2, x_410);
lean_ctor_set(x_469, 3, x_468);
lean_ctor_set(x_469, 4, x_467);
lean_ctor_set(x_469, 5, x_37);
lean_ctor_set_uint8(x_469, sizeof(void*)*6, x_413);
lean_ctor_set_uint8(x_469, sizeof(void*)*6 + 1, x_28);
x_470 = lean_apply_6(x_437, x_469, x_2, x_3, x_4, x_5, x_436);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_410);
lean_dec(x_402);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_471 = lean_ctor_get(x_434, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_434, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_473 = x_434;
} else {
 lean_dec_ref(x_434);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_475 = lean_ctor_get(x_429, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_429, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 x_477 = x_429;
} else {
 lean_dec_ref(x_429);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_476);
return x_478;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_479 = lean_ctor_get(x_426, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_426, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_480);
return x_482;
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_483 = lean_ctor_get(x_423, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_423, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_485 = x_423;
} else {
 lean_dec_ref(x_423);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_484);
return x_486;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_487 = lean_ctor_get(x_419, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_419, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_489 = x_419;
} else {
 lean_dec_ref(x_419);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_410);
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_491 = lean_ctor_get(x_414, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_414, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_493 = x_414;
} else {
 lean_dec_ref(x_414);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_406);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_495 = lean_ctor_get(x_409, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_409, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_497 = x_409;
} else {
 lean_dec_ref(x_409);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_free_object(x_29);
x_499 = l_Lean_ConstantInfo_type(x_27);
x_500 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_501 = lean_st_mk_ref(x_500, x_388);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_504 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_502);
x_505 = l_Lean_Compiler_LCNF_toLCNFType(x_499, x_504, x_502, x_4, x_5, x_503);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; lean_object* x_521; lean_object* x_522; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_st_ref_get(x_502, x_507);
lean_dec(x_502);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_510 = x_508;
} else {
 lean_dec_ref(x_508);
 x_510 = lean_box(0);
}
x_511 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_506);
if (lean_is_scalar(x_510)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_510;
}
lean_ctor_set(x_512, 0, x_506);
lean_ctor_set(x_512, 1, x_511);
x_513 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_512, x_2, x_3, x_4, x_5, x_509);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
x_517 = lean_ctor_get(x_514, 1);
lean_inc(x_517);
lean_dec(x_514);
x_518 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_519 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_520 = 0;
x_521 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_521, 0, x_8);
lean_ctor_set(x_521, 1, x_518);
lean_ctor_set(x_521, 2, x_506);
lean_ctor_set(x_521, 3, x_517);
lean_ctor_set(x_521, 4, x_519);
lean_ctor_set(x_521, 5, x_37);
lean_ctor_set_uint8(x_521, sizeof(void*)*6, x_520);
lean_ctor_set_uint8(x_521, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_516)) {
 x_522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_522 = x_516;
}
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_515);
return x_522;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_502);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_523 = lean_ctor_get(x_505, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_505, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_525 = x_505;
} else {
 lean_dec_ref(x_505);
 x_525 = lean_box(0);
}
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(1, 2, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_523);
lean_ctor_set(x_526, 1, x_524);
return x_526;
}
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_389);
lean_free_object(x_29);
x_527 = lean_ctor_get(x_392, 0);
lean_inc(x_527);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 x_528 = x_392;
} else {
 lean_dec_ref(x_392);
 x_528 = lean_box(0);
}
x_529 = l_Lean_ConstantInfo_type(x_27);
x_530 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_531 = lean_st_mk_ref(x_530, x_388);
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_532);
x_535 = l_Lean_Compiler_LCNF_toLCNFType(x_529, x_534, x_532, x_4, x_5, x_533);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; lean_object* x_552; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_st_ref_get(x_532, x_537);
lean_dec(x_532);
x_539 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_540 = x_538;
} else {
 lean_dec_ref(x_538);
 x_540 = lean_box(0);
}
x_541 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_536);
if (lean_is_scalar(x_540)) {
 x_542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_542 = x_540;
}
lean_ctor_set(x_542, 0, x_536);
lean_ctor_set(x_542, 1, x_541);
x_543 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_542, x_2, x_3, x_4, x_5, x_539);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 lean_ctor_release(x_543, 1);
 x_546 = x_543;
} else {
 lean_dec_ref(x_543);
 x_546 = lean_box(0);
}
x_547 = lean_ctor_get(x_544, 1);
lean_inc(x_547);
lean_dec(x_544);
x_548 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_528)) {
 x_549 = lean_alloc_ctor(1, 1, 0);
} else {
 x_549 = x_528;
}
lean_ctor_set(x_549, 0, x_527);
x_550 = 0;
x_551 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_551, 0, x_8);
lean_ctor_set(x_551, 1, x_548);
lean_ctor_set(x_551, 2, x_536);
lean_ctor_set(x_551, 3, x_547);
lean_ctor_set(x_551, 4, x_549);
lean_ctor_set(x_551, 5, x_37);
lean_ctor_set_uint8(x_551, sizeof(void*)*6, x_550);
lean_ctor_set_uint8(x_551, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_546)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_546;
}
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_545);
return x_552;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_532);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_553 = lean_ctor_get(x_535, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_535, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_555 = x_535;
} else {
 lean_dec_ref(x_535);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_553);
lean_ctor_set(x_556, 1, x_554);
return x_556;
}
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_557 = lean_ctor_get(x_29, 0);
x_558 = lean_ctor_get(x_29, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_29);
x_559 = lean_ctor_get(x_557, 0);
lean_inc(x_559);
lean_dec(x_557);
x_560 = l_Lean_Compiler_instInhabitedInlineAttributeKind;
x_561 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_562 = lean_box(x_560);
lean_inc(x_8);
x_563 = l_Lean_EnumAttributes_getValue___rarg(x_562, x_561, x_559, x_8);
x_564 = lean_st_ref_get(x_5, x_558);
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_567 = x_564;
} else {
 lean_dec_ref(x_564);
 x_567 = lean_box(0);
}
x_568 = lean_ctor_get(x_565, 0);
lean_inc(x_568);
lean_dec(x_565);
x_569 = l_Lean_instInhabitedExternAttrData;
x_570 = l_Lean_Compiler_LCNF_toDecl___closed__6;
lean_inc(x_8);
lean_inc(x_568);
x_571 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_569, x_570, x_568, x_8);
if (lean_obj_tag(x_571) == 0)
{
uint8_t x_572; 
lean_inc(x_8);
x_572 = l_Lean_hasInitAttr(x_568, x_8);
if (x_572 == 0)
{
uint8_t x_573; lean_object* x_574; 
x_573 = 1;
lean_inc(x_27);
x_574 = l_Lean_ConstantInfo_value_x3f(x_27, x_573);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_563);
lean_dec(x_27);
x_575 = l_Lean_MessageData_ofName(x_8);
x_576 = l_Lean_Compiler_LCNF_toDecl___closed__2;
if (lean_is_scalar(x_567)) {
 x_577 = lean_alloc_ctor(7, 2, 0);
} else {
 x_577 = x_567;
 lean_ctor_set_tag(x_577, 7);
}
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_575);
x_578 = l_Lean_Compiler_LCNF_toDecl___closed__8;
x_579 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
x_580 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_579, x_2, x_3, x_4, x_5, x_566);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_580;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_567);
x_581 = lean_ctor_get(x_574, 0);
lean_inc(x_581);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 x_582 = x_574;
} else {
 lean_dec_ref(x_574);
 x_582 = lean_box(0);
}
x_583 = l_Lean_ConstantInfo_type(x_27);
x_584 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_585 = lean_st_mk_ref(x_584, x_566);
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
x_588 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_586);
x_589 = l_Lean_Compiler_LCNF_toLCNFType(x_583, x_588, x_586, x_4, x_5, x_587);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; lean_object* x_594; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_592 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_593 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_586);
x_594 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_581, x_592, x_593, x_588, x_586, x_4, x_5, x_591);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
lean_dec(x_594);
x_597 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_598 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_599 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_595, x_597, x_598, x_4, x_5, x_596);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_603 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_600, x_602, x_598, x_4, x_5, x_601);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
lean_inc(x_5);
lean_inc(x_4);
x_606 = l_Lean_Compiler_LCNF_inlineMatchers(x_604, x_4, x_5, x_605);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
lean_inc(x_5);
lean_inc(x_4);
x_609 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_607, x_602, x_598, x_4, x_5, x_608);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_st_ref_get(x_586, x_611);
lean_dec(x_586);
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_614 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_610, x_2, x_3, x_4, x_5, x_613);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_615) == 1)
{
lean_object* x_618; 
x_618 = lean_ctor_get(x_615, 1);
lean_inc(x_618);
switch (lean_obj_tag(x_618)) {
case 4:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_582);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 x_619 = x_618;
} else {
 lean_dec_ref(x_618);
 x_619 = lean_box(0);
}
x_620 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_619)) {
 x_621 = lean_alloc_ctor(0, 1, 0);
} else {
 x_621 = x_619;
 lean_ctor_set_tag(x_621, 0);
}
lean_ctor_set(x_621, 0, x_615);
x_622 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_623 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_623, 0, x_8);
lean_ctor_set(x_623, 1, x_620);
lean_ctor_set(x_623, 2, x_590);
lean_ctor_set(x_623, 3, x_622);
lean_ctor_set(x_623, 4, x_621);
lean_ctor_set(x_623, 5, x_563);
lean_ctor_set_uint8(x_623, sizeof(void*)*6, x_593);
lean_ctor_set_uint8(x_623, sizeof(void*)*6 + 1, x_28);
x_624 = lean_apply_6(x_617, x_623, x_2, x_3, x_4, x_5, x_616);
return x_624;
}
case 5:
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_582);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 x_625 = x_618;
} else {
 lean_dec_ref(x_618);
 x_625 = lean_box(0);
}
x_626 = lean_ctor_get(x_615, 0);
lean_inc(x_626);
lean_dec(x_615);
x_627 = l_Lean_Compiler_LCNF_eraseFunDecl(x_626, x_593, x_2, x_3, x_4, x_5, x_616);
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
lean_dec(x_627);
x_629 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_630 = lean_ctor_get(x_626, 2);
lean_inc(x_630);
x_631 = lean_ctor_get(x_626, 4);
lean_inc(x_631);
lean_dec(x_626);
if (lean_is_scalar(x_625)) {
 x_632 = lean_alloc_ctor(0, 1, 0);
} else {
 x_632 = x_625;
 lean_ctor_set_tag(x_632, 0);
}
lean_ctor_set(x_632, 0, x_631);
x_633 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_633, 0, x_8);
lean_ctor_set(x_633, 1, x_629);
lean_ctor_set(x_633, 2, x_590);
lean_ctor_set(x_633, 3, x_630);
lean_ctor_set(x_633, 4, x_632);
lean_ctor_set(x_633, 5, x_563);
lean_ctor_set_uint8(x_633, sizeof(void*)*6, x_593);
lean_ctor_set_uint8(x_633, sizeof(void*)*6 + 1, x_28);
x_634 = lean_apply_6(x_617, x_633, x_2, x_3, x_4, x_5, x_628);
return x_634;
}
case 6:
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_582);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 x_635 = x_618;
} else {
 lean_dec_ref(x_618);
 x_635 = lean_box(0);
}
x_636 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_635)) {
 x_637 = lean_alloc_ctor(0, 1, 0);
} else {
 x_637 = x_635;
 lean_ctor_set_tag(x_637, 0);
}
lean_ctor_set(x_637, 0, x_615);
x_638 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_639 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_639, 0, x_8);
lean_ctor_set(x_639, 1, x_636);
lean_ctor_set(x_639, 2, x_590);
lean_ctor_set(x_639, 3, x_638);
lean_ctor_set(x_639, 4, x_637);
lean_ctor_set(x_639, 5, x_563);
lean_ctor_set_uint8(x_639, sizeof(void*)*6, x_593);
lean_ctor_set_uint8(x_639, sizeof(void*)*6 + 1, x_28);
x_640 = lean_apply_6(x_617, x_639, x_2, x_3, x_4, x_5, x_616);
return x_640;
}
default: 
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_618);
x_641 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_582)) {
 x_642 = lean_alloc_ctor(0, 1, 0);
} else {
 x_642 = x_582;
 lean_ctor_set_tag(x_642, 0);
}
lean_ctor_set(x_642, 0, x_615);
x_643 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_644 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_644, 0, x_8);
lean_ctor_set(x_644, 1, x_641);
lean_ctor_set(x_644, 2, x_590);
lean_ctor_set(x_644, 3, x_643);
lean_ctor_set(x_644, 4, x_642);
lean_ctor_set(x_644, 5, x_563);
lean_ctor_set_uint8(x_644, sizeof(void*)*6, x_593);
lean_ctor_set_uint8(x_644, sizeof(void*)*6 + 1, x_28);
x_645 = lean_apply_6(x_617, x_644, x_2, x_3, x_4, x_5, x_616);
return x_645;
}
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_646 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_582)) {
 x_647 = lean_alloc_ctor(0, 1, 0);
} else {
 x_647 = x_582;
 lean_ctor_set_tag(x_647, 0);
}
lean_ctor_set(x_647, 0, x_615);
x_648 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_649 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_649, 0, x_8);
lean_ctor_set(x_649, 1, x_646);
lean_ctor_set(x_649, 2, x_590);
lean_ctor_set(x_649, 3, x_648);
lean_ctor_set(x_649, 4, x_647);
lean_ctor_set(x_649, 5, x_563);
lean_ctor_set_uint8(x_649, sizeof(void*)*6, x_593);
lean_ctor_set_uint8(x_649, sizeof(void*)*6 + 1, x_28);
x_650 = lean_apply_6(x_617, x_649, x_2, x_3, x_4, x_5, x_616);
return x_650;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_dec(x_590);
lean_dec(x_582);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_651 = lean_ctor_get(x_614, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_614, 1);
lean_inc(x_652);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_653 = x_614;
} else {
 lean_dec_ref(x_614);
 x_653 = lean_box(0);
}
if (lean_is_scalar(x_653)) {
 x_654 = lean_alloc_ctor(1, 2, 0);
} else {
 x_654 = x_653;
}
lean_ctor_set(x_654, 0, x_651);
lean_ctor_set(x_654, 1, x_652);
return x_654;
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_582);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_655 = lean_ctor_get(x_609, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_609, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_657 = x_609;
} else {
 lean_dec_ref(x_609);
 x_657 = lean_box(0);
}
if (lean_is_scalar(x_657)) {
 x_658 = lean_alloc_ctor(1, 2, 0);
} else {
 x_658 = x_657;
}
lean_ctor_set(x_658, 0, x_655);
lean_ctor_set(x_658, 1, x_656);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_582);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_659 = lean_ctor_get(x_606, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_606, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_661 = x_606;
} else {
 lean_dec_ref(x_606);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(1, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_659);
lean_ctor_set(x_662, 1, x_660);
return x_662;
}
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_582);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_663 = lean_ctor_get(x_603, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_603, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_665 = x_603;
} else {
 lean_dec_ref(x_603);
 x_665 = lean_box(0);
}
if (lean_is_scalar(x_665)) {
 x_666 = lean_alloc_ctor(1, 2, 0);
} else {
 x_666 = x_665;
}
lean_ctor_set(x_666, 0, x_663);
lean_ctor_set(x_666, 1, x_664);
return x_666;
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_582);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_667 = lean_ctor_get(x_599, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_599, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_669 = x_599;
} else {
 lean_dec_ref(x_599);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_667);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_582);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_671 = lean_ctor_get(x_594, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_594, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_673 = x_594;
} else {
 lean_dec_ref(x_594);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(1, 2, 0);
} else {
 x_674 = x_673;
}
lean_ctor_set(x_674, 0, x_671);
lean_ctor_set(x_674, 1, x_672);
return x_674;
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_586);
lean_dec(x_582);
lean_dec(x_581);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_675 = lean_ctor_get(x_589, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_589, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_677 = x_589;
} else {
 lean_dec_ref(x_589);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(1, 2, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_675);
lean_ctor_set(x_678, 1, x_676);
return x_678;
}
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
lean_dec(x_567);
x_679 = l_Lean_ConstantInfo_type(x_27);
x_680 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_681 = lean_st_mk_ref(x_680, x_566);
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_684 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_682);
x_685 = l_Lean_Compiler_LCNF_toLCNFType(x_679, x_684, x_682, x_4, x_5, x_683);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; uint8_t x_700; lean_object* x_701; lean_object* x_702; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
x_688 = lean_st_ref_get(x_682, x_687);
lean_dec(x_682);
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_690 = x_688;
} else {
 lean_dec_ref(x_688);
 x_690 = lean_box(0);
}
x_691 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_686);
if (lean_is_scalar(x_690)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_690;
}
lean_ctor_set(x_692, 0, x_686);
lean_ctor_set(x_692, 1, x_691);
x_693 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_692, x_2, x_3, x_4, x_5, x_689);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_696 = x_693;
} else {
 lean_dec_ref(x_693);
 x_696 = lean_box(0);
}
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_699 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_700 = 0;
x_701 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_701, 0, x_8);
lean_ctor_set(x_701, 1, x_698);
lean_ctor_set(x_701, 2, x_686);
lean_ctor_set(x_701, 3, x_697);
lean_ctor_set(x_701, 4, x_699);
lean_ctor_set(x_701, 5, x_563);
lean_ctor_set_uint8(x_701, sizeof(void*)*6, x_700);
lean_ctor_set_uint8(x_701, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_696)) {
 x_702 = lean_alloc_ctor(0, 2, 0);
} else {
 x_702 = x_696;
}
lean_ctor_set(x_702, 0, x_701);
lean_ctor_set(x_702, 1, x_695);
return x_702;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_682);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_703 = lean_ctor_get(x_685, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_685, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_705 = x_685;
} else {
 lean_dec_ref(x_685);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_703);
lean_ctor_set(x_706, 1, x_704);
return x_706;
}
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_dec(x_568);
lean_dec(x_567);
x_707 = lean_ctor_get(x_571, 0);
lean_inc(x_707);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_708 = x_571;
} else {
 lean_dec_ref(x_571);
 x_708 = lean_box(0);
}
x_709 = l_Lean_ConstantInfo_type(x_27);
x_710 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_711 = lean_st_mk_ref(x_710, x_566);
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
x_714 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_712);
x_715 = l_Lean_Compiler_LCNF_toLCNFType(x_709, x_714, x_712, x_4, x_5, x_713);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; lean_object* x_732; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = lean_st_ref_get(x_712, x_717);
lean_dec(x_712);
x_719 = lean_ctor_get(x_718, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_720 = x_718;
} else {
 lean_dec_ref(x_718);
 x_720 = lean_box(0);
}
x_721 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_716);
if (lean_is_scalar(x_720)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_720;
}
lean_ctor_set(x_722, 0, x_716);
lean_ctor_set(x_722, 1, x_721);
x_723 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_722, x_2, x_3, x_4, x_5, x_719);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_726 = x_723;
} else {
 lean_dec_ref(x_723);
 x_726 = lean_box(0);
}
x_727 = lean_ctor_get(x_724, 1);
lean_inc(x_727);
lean_dec(x_724);
x_728 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_708)) {
 x_729 = lean_alloc_ctor(1, 1, 0);
} else {
 x_729 = x_708;
}
lean_ctor_set(x_729, 0, x_707);
x_730 = 0;
x_731 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_731, 0, x_8);
lean_ctor_set(x_731, 1, x_728);
lean_ctor_set(x_731, 2, x_716);
lean_ctor_set(x_731, 3, x_727);
lean_ctor_set(x_731, 4, x_729);
lean_ctor_set(x_731, 5, x_563);
lean_ctor_set_uint8(x_731, sizeof(void*)*6, x_730);
lean_ctor_set_uint8(x_731, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_726)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_726;
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_725);
return x_732;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_712);
lean_dec(x_708);
lean_dec(x_707);
lean_dec(x_563);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_733 = lean_ctor_get(x_715, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_715, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_735 = x_715;
} else {
 lean_dec_ref(x_715);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_toDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
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
l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1);
l_Lean_Compiler_LCNF_inlineMatchers___closed__1 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__1);
l_Lean_Compiler_LCNF_inlineMatchers___closed__2 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__2();
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
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1);
l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1);
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
l_Lean_Compiler_LCNF_toDecl___closed__9 = _init_l_Lean_Compiler_LCNF_toDecl___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__9);
l_Lean_Compiler_LCNF_toDecl___closed__10 = _init_l_Lean_Compiler_LCNF_toDecl___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__10);
l_Lean_Compiler_LCNF_toDecl___closed__11 = _init_l_Lean_Compiler_LCNF_toDecl___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__11);
l_Lean_Compiler_LCNF_toDecl___closed__12 = _init_l_Lean_Compiler_LCNF_toDecl___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__12);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
