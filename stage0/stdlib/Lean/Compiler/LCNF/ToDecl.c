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
goto block_565;
}
else
{
lean_object* x_566; 
lean_dec(x_1);
x_566 = lean_ctor_get(x_7, 0);
lean_inc(x_566);
lean_dec(x_7);
x_8 = x_566;
goto block_565;
}
block_565:
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_560; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_27 = x_9;
} else {
 lean_dec_ref(x_9);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_560 = l_Lean_ConstantInfo_isPartial(x_28);
if (x_560 == 0)
{
uint8_t x_561; 
x_561 = l_Lean_ConstantInfo_isUnsafe(x_28);
if (x_561 == 0)
{
uint8_t x_562; 
x_562 = 1;
x_29 = x_562;
goto block_559;
}
else
{
uint8_t x_563; 
x_563 = 0;
x_29 = x_563;
goto block_559;
}
}
else
{
uint8_t x_564; 
x_564 = 0;
x_29 = x_564;
goto block_559;
}
block_559:
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_st_ref_get(x_5, x_26);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Compiler_instInhabitedInlineAttributeKind;
x_36 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_37 = lean_box(x_35);
lean_inc(x_8);
lean_inc(x_34);
x_38 = l_Lean_EnumAttributes_getValue___rarg(x_37, x_36, x_34, x_8);
x_39 = l_Lean_instInhabitedExternAttrData;
x_40 = l_Lean_Compiler_LCNF_toDecl___closed__6;
lean_inc(x_8);
lean_inc(x_34);
x_41 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_39, x_40, x_34, x_8);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_inc(x_8);
x_42 = l_Lean_hasInitAttr(x_34, x_8);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; 
x_43 = 1;
lean_inc(x_28);
x_44 = l_Lean_ConstantInfo_value_x3f(x_28, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_38);
lean_dec(x_28);
x_45 = l_Lean_MessageData_ofName(x_8);
x_46 = l_Lean_Compiler_LCNF_toDecl___closed__2;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_45);
lean_ctor_set(x_30, 0, x_46);
x_47 = l_Lean_Compiler_LCNF_toDecl___closed__8;
if (lean_is_scalar(x_27)) {
 x_48 = lean_alloc_ctor(7, 2, 0);
} else {
 x_48 = x_27;
 lean_ctor_set_tag(x_48, 7);
}
lean_ctor_set(x_48, 0, x_30);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_48, x_2, x_3, x_4, x_5, x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_49;
}
else
{
uint8_t x_50; 
lean_free_object(x_30);
lean_dec(x_27);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = l_Lean_ConstantInfo_type(x_28);
x_53 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_54 = lean_st_mk_ref(x_53, x_33);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_55);
x_58 = l_Lean_Compiler_LCNF_toLCNFType(x_52, x_57, x_55, x_4, x_5, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_62 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_55);
x_63 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_51, x_61, x_62, x_57, x_55, x_4, x_5, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_67 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_68 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_64, x_66, x_67, x_4, x_5, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_72 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_69, x_71, x_67, x_4, x_5, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_5);
lean_inc(x_4);
x_75 = l_Lean_Compiler_LCNF_inlineMatchers(x_73, x_4, x_5, x_74);
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
x_78 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_76, x_71, x_67, x_4, x_5, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_st_ref_get(x_55, x_80);
lean_dec(x_55);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_79, x_2, x_3, x_4, x_5, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
switch (lean_obj_tag(x_87)) {
case 4:
{
uint8_t x_88; 
lean_free_object(x_44);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_84);
x_91 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_92 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_92, 0, x_8);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_59);
lean_ctor_set(x_92, 3, x_91);
lean_ctor_set(x_92, 4, x_87);
lean_ctor_set(x_92, 5, x_38);
lean_ctor_set_uint8(x_92, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_92, sizeof(void*)*6 + 1, x_29);
x_93 = lean_apply_6(x_86, x_92, x_2, x_3, x_4, x_5, x_85);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_87);
x_94 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_84);
x_96 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_97 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_97, 0, x_8);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_59);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set(x_97, 4, x_95);
lean_ctor_set(x_97, 5, x_38);
lean_ctor_set_uint8(x_97, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_97, sizeof(void*)*6 + 1, x_29);
x_98 = lean_apply_6(x_86, x_97, x_2, x_3, x_4, x_5, x_85);
return x_98;
}
}
case 5:
{
uint8_t x_99; 
lean_free_object(x_44);
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_87, 0);
lean_dec(x_100);
x_101 = lean_ctor_get(x_84, 0);
lean_inc(x_101);
lean_dec(x_84);
x_102 = l_Lean_Compiler_LCNF_eraseFunDecl(x_101, x_62, x_2, x_3, x_4, x_5, x_85);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_105 = lean_ctor_get(x_101, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_101, 4);
lean_inc(x_106);
lean_dec(x_101);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_106);
x_107 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_107, 0, x_8);
lean_ctor_set(x_107, 1, x_104);
lean_ctor_set(x_107, 2, x_59);
lean_ctor_set(x_107, 3, x_105);
lean_ctor_set(x_107, 4, x_87);
lean_ctor_set(x_107, 5, x_38);
lean_ctor_set_uint8(x_107, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_107, sizeof(void*)*6 + 1, x_29);
x_108 = lean_apply_6(x_86, x_107, x_2, x_3, x_4, x_5, x_103);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_87);
x_109 = lean_ctor_get(x_84, 0);
lean_inc(x_109);
lean_dec(x_84);
x_110 = l_Lean_Compiler_LCNF_eraseFunDecl(x_109, x_62, x_2, x_3, x_4, x_5, x_85);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_113 = lean_ctor_get(x_109, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 4);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_116, 0, x_8);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_59);
lean_ctor_set(x_116, 3, x_113);
lean_ctor_set(x_116, 4, x_115);
lean_ctor_set(x_116, 5, x_38);
lean_ctor_set_uint8(x_116, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_116, sizeof(void*)*6 + 1, x_29);
x_117 = lean_apply_6(x_86, x_116, x_2, x_3, x_4, x_5, x_111);
return x_117;
}
}
case 6:
{
uint8_t x_118; 
lean_free_object(x_44);
x_118 = !lean_is_exclusive(x_87);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_87, 0);
lean_dec(x_119);
x_120 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_84);
x_121 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_122 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_122, 0, x_8);
lean_ctor_set(x_122, 1, x_120);
lean_ctor_set(x_122, 2, x_59);
lean_ctor_set(x_122, 3, x_121);
lean_ctor_set(x_122, 4, x_87);
lean_ctor_set(x_122, 5, x_38);
lean_ctor_set_uint8(x_122, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_122, sizeof(void*)*6 + 1, x_29);
x_123 = lean_apply_6(x_86, x_122, x_2, x_3, x_4, x_5, x_85);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_87);
x_124 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_84);
x_126 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_127 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_127, 0, x_8);
lean_ctor_set(x_127, 1, x_124);
lean_ctor_set(x_127, 2, x_59);
lean_ctor_set(x_127, 3, x_126);
lean_ctor_set(x_127, 4, x_125);
lean_ctor_set(x_127, 5, x_38);
lean_ctor_set_uint8(x_127, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_127, sizeof(void*)*6 + 1, x_29);
x_128 = lean_apply_6(x_86, x_127, x_2, x_3, x_4, x_5, x_85);
return x_128;
}
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_87);
x_129 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_84);
x_130 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_131 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_131, 0, x_8);
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 2, x_59);
lean_ctor_set(x_131, 3, x_130);
lean_ctor_set(x_131, 4, x_44);
lean_ctor_set(x_131, 5, x_38);
lean_ctor_set_uint8(x_131, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_131, sizeof(void*)*6 + 1, x_29);
x_132 = lean_apply_6(x_86, x_131, x_2, x_3, x_4, x_5, x_85);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_84);
x_134 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_135 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_135, 0, x_8);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_59);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_44);
lean_ctor_set(x_135, 5, x_38);
lean_ctor_set_uint8(x_135, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_135, sizeof(void*)*6 + 1, x_29);
x_136 = lean_apply_6(x_86, x_135, x_2, x_3, x_4, x_5, x_85);
return x_136;
}
}
else
{
uint8_t x_137; 
lean_dec(x_59);
lean_free_object(x_44);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_83);
if (x_137 == 0)
{
return x_83;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_83, 0);
x_139 = lean_ctor_get(x_83, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_83);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_59);
lean_dec(x_55);
lean_free_object(x_44);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_78);
if (x_141 == 0)
{
return x_78;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_78, 0);
x_143 = lean_ctor_get(x_78, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_78);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_59);
lean_dec(x_55);
lean_free_object(x_44);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_75);
if (x_145 == 0)
{
return x_75;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_75, 0);
x_147 = lean_ctor_get(x_75, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_75);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_59);
lean_dec(x_55);
lean_free_object(x_44);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_72);
if (x_149 == 0)
{
return x_72;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_72, 0);
x_151 = lean_ctor_get(x_72, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_72);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_59);
lean_dec(x_55);
lean_free_object(x_44);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_68);
if (x_153 == 0)
{
return x_68;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_68, 0);
x_155 = lean_ctor_get(x_68, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_68);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_59);
lean_dec(x_55);
lean_free_object(x_44);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_63);
if (x_157 == 0)
{
return x_63;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_63, 0);
x_159 = lean_ctor_get(x_63, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_63);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_55);
lean_free_object(x_44);
lean_dec(x_51);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_58);
if (x_161 == 0)
{
return x_58;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_58, 0);
x_163 = lean_ctor_get(x_58, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_58);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_44, 0);
lean_inc(x_165);
lean_dec(x_44);
x_166 = l_Lean_ConstantInfo_type(x_28);
x_167 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_168 = lean_st_mk_ref(x_167, x_33);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_169);
x_172 = l_Lean_Compiler_LCNF_toLCNFType(x_166, x_171, x_169, x_4, x_5, x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_176 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_169);
x_177 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_165, x_175, x_176, x_171, x_169, x_4, x_5, x_174);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_181 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_182 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_178, x_180, x_181, x_4, x_5, x_179);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_186 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_183, x_185, x_181, x_4, x_5, x_184);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_5);
lean_inc(x_4);
x_189 = l_Lean_Compiler_LCNF_inlineMatchers(x_187, x_4, x_5, x_188);
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
x_192 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_190, x_185, x_181, x_4, x_5, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_get(x_169, x_194);
lean_dec(x_169);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_197 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_193, x_2, x_3, x_4, x_5, x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_198) == 1)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
switch (lean_obj_tag(x_201)) {
case 4:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_202 = x_201;
} else {
 lean_dec_ref(x_201);
 x_202 = lean_box(0);
}
x_203 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 1, 0);
} else {
 x_204 = x_202;
 lean_ctor_set_tag(x_204, 0);
}
lean_ctor_set(x_204, 0, x_198);
x_205 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_206 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_206, 0, x_8);
lean_ctor_set(x_206, 1, x_203);
lean_ctor_set(x_206, 2, x_173);
lean_ctor_set(x_206, 3, x_205);
lean_ctor_set(x_206, 4, x_204);
lean_ctor_set(x_206, 5, x_38);
lean_ctor_set_uint8(x_206, sizeof(void*)*6, x_176);
lean_ctor_set_uint8(x_206, sizeof(void*)*6 + 1, x_29);
x_207 = lean_apply_6(x_200, x_206, x_2, x_3, x_4, x_5, x_199);
return x_207;
}
case 5:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_208 = x_201;
} else {
 lean_dec_ref(x_201);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_198, 0);
lean_inc(x_209);
lean_dec(x_198);
x_210 = l_Lean_Compiler_LCNF_eraseFunDecl(x_209, x_176, x_2, x_3, x_4, x_5, x_199);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_213 = lean_ctor_get(x_209, 2);
lean_inc(x_213);
x_214 = lean_ctor_get(x_209, 4);
lean_inc(x_214);
lean_dec(x_209);
if (lean_is_scalar(x_208)) {
 x_215 = lean_alloc_ctor(0, 1, 0);
} else {
 x_215 = x_208;
 lean_ctor_set_tag(x_215, 0);
}
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_216, 0, x_8);
lean_ctor_set(x_216, 1, x_212);
lean_ctor_set(x_216, 2, x_173);
lean_ctor_set(x_216, 3, x_213);
lean_ctor_set(x_216, 4, x_215);
lean_ctor_set(x_216, 5, x_38);
lean_ctor_set_uint8(x_216, sizeof(void*)*6, x_176);
lean_ctor_set_uint8(x_216, sizeof(void*)*6 + 1, x_29);
x_217 = lean_apply_6(x_200, x_216, x_2, x_3, x_4, x_5, x_211);
return x_217;
}
case 6:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_218 = x_201;
} else {
 lean_dec_ref(x_201);
 x_218 = lean_box(0);
}
x_219 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 1, 0);
} else {
 x_220 = x_218;
 lean_ctor_set_tag(x_220, 0);
}
lean_ctor_set(x_220, 0, x_198);
x_221 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_222 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_222, 0, x_8);
lean_ctor_set(x_222, 1, x_219);
lean_ctor_set(x_222, 2, x_173);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_222, 4, x_220);
lean_ctor_set(x_222, 5, x_38);
lean_ctor_set_uint8(x_222, sizeof(void*)*6, x_176);
lean_ctor_set_uint8(x_222, sizeof(void*)*6 + 1, x_29);
x_223 = lean_apply_6(x_200, x_222, x_2, x_3, x_4, x_5, x_199);
return x_223;
}
default: 
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_201);
x_224 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_198);
x_226 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_227 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_227, 0, x_8);
lean_ctor_set(x_227, 1, x_224);
lean_ctor_set(x_227, 2, x_173);
lean_ctor_set(x_227, 3, x_226);
lean_ctor_set(x_227, 4, x_225);
lean_ctor_set(x_227, 5, x_38);
lean_ctor_set_uint8(x_227, sizeof(void*)*6, x_176);
lean_ctor_set_uint8(x_227, sizeof(void*)*6 + 1, x_29);
x_228 = lean_apply_6(x_200, x_227, x_2, x_3, x_4, x_5, x_199);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_198);
x_231 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_232 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_232, 0, x_8);
lean_ctor_set(x_232, 1, x_229);
lean_ctor_set(x_232, 2, x_173);
lean_ctor_set(x_232, 3, x_231);
lean_ctor_set(x_232, 4, x_230);
lean_ctor_set(x_232, 5, x_38);
lean_ctor_set_uint8(x_232, sizeof(void*)*6, x_176);
lean_ctor_set_uint8(x_232, sizeof(void*)*6 + 1, x_29);
x_233 = lean_apply_6(x_200, x_232, x_2, x_3, x_4, x_5, x_199);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_173);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_234 = lean_ctor_get(x_197, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_197, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_236 = x_197;
} else {
 lean_dec_ref(x_197);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_173);
lean_dec(x_169);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_238 = lean_ctor_get(x_192, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_192, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_240 = x_192;
} else {
 lean_dec_ref(x_192);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_173);
lean_dec(x_169);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = lean_ctor_get(x_189, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_189, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_244 = x_189;
} else {
 lean_dec_ref(x_189);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_173);
lean_dec(x_169);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_ctor_get(x_186, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_186, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_248 = x_186;
} else {
 lean_dec_ref(x_186);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_173);
lean_dec(x_169);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_250 = lean_ctor_get(x_182, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_182, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_252 = x_182;
} else {
 lean_dec_ref(x_182);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_173);
lean_dec(x_169);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_254 = lean_ctor_get(x_177, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_177, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_256 = x_177;
} else {
 lean_dec_ref(x_177);
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
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_169);
lean_dec(x_165);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_258 = lean_ctor_get(x_172, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_172, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_260 = x_172;
} else {
 lean_dec_ref(x_172);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_free_object(x_30);
lean_dec(x_27);
x_262 = l_Lean_ConstantInfo_type(x_28);
x_263 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_264 = lean_st_mk_ref(x_263, x_33);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_265);
x_268 = l_Lean_Compiler_LCNF_toLCNFType(x_262, x_267, x_265, x_4, x_5, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_st_ref_get(x_265, x_270);
lean_dec(x_265);
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_271, 1);
x_274 = lean_ctor_get(x_271, 0);
lean_dec(x_274);
x_275 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_269);
lean_ctor_set(x_271, 1, x_275);
lean_ctor_set(x_271, 0, x_269);
x_276 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_271, x_2, x_3, x_4, x_5, x_273);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_281 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_282 = 0;
x_283 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_283, 0, x_8);
lean_ctor_set(x_283, 1, x_280);
lean_ctor_set(x_283, 2, x_269);
lean_ctor_set(x_283, 3, x_279);
lean_ctor_set(x_283, 4, x_281);
lean_ctor_set(x_283, 5, x_38);
lean_ctor_set_uint8(x_283, sizeof(void*)*6, x_282);
lean_ctor_set_uint8(x_283, sizeof(void*)*6 + 1, x_29);
lean_ctor_set(x_276, 0, x_283);
return x_276;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; 
x_284 = lean_ctor_get(x_276, 0);
x_285 = lean_ctor_get(x_276, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_276);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_288 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_289 = 0;
x_290 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_290, 0, x_8);
lean_ctor_set(x_290, 1, x_287);
lean_ctor_set(x_290, 2, x_269);
lean_ctor_set(x_290, 3, x_286);
lean_ctor_set(x_290, 4, x_288);
lean_ctor_set(x_290, 5, x_38);
lean_ctor_set_uint8(x_290, sizeof(void*)*6, x_289);
lean_ctor_set_uint8(x_290, sizeof(void*)*6 + 1, x_29);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_285);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; 
x_292 = lean_ctor_get(x_271, 1);
lean_inc(x_292);
lean_dec(x_271);
x_293 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_269);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_269);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_294, x_2, x_3, x_4, x_5, x_292);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_298 = x_295;
} else {
 lean_dec_ref(x_295);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
lean_dec(x_296);
x_300 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_301 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_302 = 0;
x_303 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_303, 0, x_8);
lean_ctor_set(x_303, 1, x_300);
lean_ctor_set(x_303, 2, x_269);
lean_ctor_set(x_303, 3, x_299);
lean_ctor_set(x_303, 4, x_301);
lean_ctor_set(x_303, 5, x_38);
lean_ctor_set_uint8(x_303, sizeof(void*)*6, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*6 + 1, x_29);
if (lean_is_scalar(x_298)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_298;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_297);
return x_304;
}
}
else
{
uint8_t x_305; 
lean_dec(x_265);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_305 = !lean_is_exclusive(x_268);
if (x_305 == 0)
{
return x_268;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_268, 0);
x_307 = lean_ctor_get(x_268, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_268);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_34);
lean_free_object(x_30);
lean_dec(x_27);
x_309 = !lean_is_exclusive(x_41);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_310 = lean_ctor_get(x_41, 0);
x_311 = l_Lean_ConstantInfo_type(x_28);
x_312 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_313 = lean_st_mk_ref(x_312, x_33);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_314);
x_317 = l_Lean_Compiler_LCNF_toLCNFType(x_311, x_316, x_314, x_4, x_5, x_315);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_st_ref_get(x_314, x_319);
lean_dec(x_314);
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_322 = lean_ctor_get(x_320, 1);
x_323 = lean_ctor_get(x_320, 0);
lean_dec(x_323);
x_324 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_318);
lean_ctor_set(x_320, 1, x_324);
lean_ctor_set(x_320, 0, x_318);
x_325 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_320, x_2, x_3, x_4, x_5, x_322);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_325, 0);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_329 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_330 = 0;
x_331 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_331, 0, x_8);
lean_ctor_set(x_331, 1, x_329);
lean_ctor_set(x_331, 2, x_318);
lean_ctor_set(x_331, 3, x_328);
lean_ctor_set(x_331, 4, x_41);
lean_ctor_set(x_331, 5, x_38);
lean_ctor_set_uint8(x_331, sizeof(void*)*6, x_330);
lean_ctor_set_uint8(x_331, sizeof(void*)*6 + 1, x_29);
lean_ctor_set(x_325, 0, x_331);
return x_325;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; 
x_332 = lean_ctor_get(x_325, 0);
x_333 = lean_ctor_get(x_325, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_325);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_336 = 0;
x_337 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_337, 0, x_8);
lean_ctor_set(x_337, 1, x_335);
lean_ctor_set(x_337, 2, x_318);
lean_ctor_set(x_337, 3, x_334);
lean_ctor_set(x_337, 4, x_41);
lean_ctor_set(x_337, 5, x_38);
lean_ctor_set_uint8(x_337, sizeof(void*)*6, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*6 + 1, x_29);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_333);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; 
x_339 = lean_ctor_get(x_320, 1);
lean_inc(x_339);
lean_dec(x_320);
x_340 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_318);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_318);
lean_ctor_set(x_341, 1, x_340);
x_342 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_341, x_2, x_3, x_4, x_5, x_339);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
lean_dec(x_343);
x_347 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_348 = 0;
x_349 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_349, 0, x_8);
lean_ctor_set(x_349, 1, x_347);
lean_ctor_set(x_349, 2, x_318);
lean_ctor_set(x_349, 3, x_346);
lean_ctor_set(x_349, 4, x_41);
lean_ctor_set(x_349, 5, x_38);
lean_ctor_set_uint8(x_349, sizeof(void*)*6, x_348);
lean_ctor_set_uint8(x_349, sizeof(void*)*6 + 1, x_29);
if (lean_is_scalar(x_345)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_345;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_344);
return x_350;
}
}
else
{
uint8_t x_351; 
lean_dec(x_314);
lean_free_object(x_41);
lean_dec(x_310);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_351 = !lean_is_exclusive(x_317);
if (x_351 == 0)
{
return x_317;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_317, 0);
x_353 = lean_ctor_get(x_317, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_317);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_355 = lean_ctor_get(x_41, 0);
lean_inc(x_355);
lean_dec(x_41);
x_356 = l_Lean_ConstantInfo_type(x_28);
x_357 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_358 = lean_st_mk_ref(x_357, x_33);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_359);
x_362 = l_Lean_Compiler_LCNF_toLCNFType(x_356, x_361, x_359, x_4, x_5, x_360);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = lean_st_ref_get(x_359, x_364);
lean_dec(x_359);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_363);
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_363);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_369, x_2, x_3, x_4, x_5, x_366);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
lean_dec(x_371);
x_375 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_355);
x_377 = 0;
x_378 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_378, 0, x_8);
lean_ctor_set(x_378, 1, x_375);
lean_ctor_set(x_378, 2, x_363);
lean_ctor_set(x_378, 3, x_374);
lean_ctor_set(x_378, 4, x_376);
lean_ctor_set(x_378, 5, x_38);
lean_ctor_set_uint8(x_378, sizeof(void*)*6, x_377);
lean_ctor_set_uint8(x_378, sizeof(void*)*6 + 1, x_29);
if (lean_is_scalar(x_373)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_373;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_372);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_359);
lean_dec(x_355);
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_380 = lean_ctor_get(x_362, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_362, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_382 = x_362;
} else {
 lean_dec_ref(x_362);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_384 = lean_ctor_get(x_30, 0);
x_385 = lean_ctor_get(x_30, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_30);
x_386 = lean_ctor_get(x_384, 0);
lean_inc(x_386);
lean_dec(x_384);
x_387 = l_Lean_Compiler_instInhabitedInlineAttributeKind;
x_388 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_389 = lean_box(x_387);
lean_inc(x_8);
lean_inc(x_386);
x_390 = l_Lean_EnumAttributes_getValue___rarg(x_389, x_388, x_386, x_8);
x_391 = l_Lean_instInhabitedExternAttrData;
x_392 = l_Lean_Compiler_LCNF_toDecl___closed__6;
lean_inc(x_8);
lean_inc(x_386);
x_393 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_391, x_392, x_386, x_8);
if (lean_obj_tag(x_393) == 0)
{
uint8_t x_394; 
lean_inc(x_8);
x_394 = l_Lean_hasInitAttr(x_386, x_8);
if (x_394 == 0)
{
uint8_t x_395; lean_object* x_396; 
x_395 = 1;
lean_inc(x_28);
x_396 = l_Lean_ConstantInfo_value_x3f(x_28, x_395);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_390);
lean_dec(x_28);
x_397 = l_Lean_MessageData_ofName(x_8);
x_398 = l_Lean_Compiler_LCNF_toDecl___closed__2;
x_399 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_397);
x_400 = l_Lean_Compiler_LCNF_toDecl___closed__8;
if (lean_is_scalar(x_27)) {
 x_401 = lean_alloc_ctor(7, 2, 0);
} else {
 x_401 = x_27;
 lean_ctor_set_tag(x_401, 7);
}
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
x_402 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_401, x_2, x_3, x_4, x_5, x_385);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_27);
x_403 = lean_ctor_get(x_396, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_404 = x_396;
} else {
 lean_dec_ref(x_396);
 x_404 = lean_box(0);
}
x_405 = l_Lean_ConstantInfo_type(x_28);
x_406 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_407 = lean_st_mk_ref(x_406, x_385);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_408);
x_411 = l_Lean_Compiler_LCNF_toLCNFType(x_405, x_410, x_408, x_4, x_5, x_409);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_415 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_408);
x_416 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_403, x_414, x_415, x_410, x_408, x_4, x_5, x_413);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_420 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_421 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_417, x_419, x_420, x_4, x_5, x_418);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_425 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_422, x_424, x_420, x_4, x_5, x_423);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
lean_inc(x_5);
lean_inc(x_4);
x_428 = l_Lean_Compiler_LCNF_inlineMatchers(x_426, x_4, x_5, x_427);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
lean_inc(x_5);
lean_inc(x_4);
x_431 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_429, x_424, x_420, x_4, x_5, x_430);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_st_ref_get(x_408, x_433);
lean_dec(x_408);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_436 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_432, x_2, x_3, x_4, x_5, x_435);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_437) == 1)
{
lean_object* x_440; 
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_440);
switch (lean_obj_tag(x_440)) {
case 4:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_404);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_441 = x_440;
} else {
 lean_dec_ref(x_440);
 x_441 = lean_box(0);
}
x_442 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(0, 1, 0);
} else {
 x_443 = x_441;
 lean_ctor_set_tag(x_443, 0);
}
lean_ctor_set(x_443, 0, x_437);
x_444 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_445 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_445, 0, x_8);
lean_ctor_set(x_445, 1, x_442);
lean_ctor_set(x_445, 2, x_412);
lean_ctor_set(x_445, 3, x_444);
lean_ctor_set(x_445, 4, x_443);
lean_ctor_set(x_445, 5, x_390);
lean_ctor_set_uint8(x_445, sizeof(void*)*6, x_415);
lean_ctor_set_uint8(x_445, sizeof(void*)*6 + 1, x_29);
x_446 = lean_apply_6(x_439, x_445, x_2, x_3, x_4, x_5, x_438);
return x_446;
}
case 5:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_404);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_447 = x_440;
} else {
 lean_dec_ref(x_440);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_437, 0);
lean_inc(x_448);
lean_dec(x_437);
x_449 = l_Lean_Compiler_LCNF_eraseFunDecl(x_448, x_415, x_2, x_3, x_4, x_5, x_438);
x_450 = lean_ctor_get(x_449, 1);
lean_inc(x_450);
lean_dec(x_449);
x_451 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_452 = lean_ctor_get(x_448, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_448, 4);
lean_inc(x_453);
lean_dec(x_448);
if (lean_is_scalar(x_447)) {
 x_454 = lean_alloc_ctor(0, 1, 0);
} else {
 x_454 = x_447;
 lean_ctor_set_tag(x_454, 0);
}
lean_ctor_set(x_454, 0, x_453);
x_455 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_455, 0, x_8);
lean_ctor_set(x_455, 1, x_451);
lean_ctor_set(x_455, 2, x_412);
lean_ctor_set(x_455, 3, x_452);
lean_ctor_set(x_455, 4, x_454);
lean_ctor_set(x_455, 5, x_390);
lean_ctor_set_uint8(x_455, sizeof(void*)*6, x_415);
lean_ctor_set_uint8(x_455, sizeof(void*)*6 + 1, x_29);
x_456 = lean_apply_6(x_439, x_455, x_2, x_3, x_4, x_5, x_450);
return x_456;
}
case 6:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_404);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_457 = x_440;
} else {
 lean_dec_ref(x_440);
 x_457 = lean_box(0);
}
x_458 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(0, 1, 0);
} else {
 x_459 = x_457;
 lean_ctor_set_tag(x_459, 0);
}
lean_ctor_set(x_459, 0, x_437);
x_460 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_461 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_461, 0, x_8);
lean_ctor_set(x_461, 1, x_458);
lean_ctor_set(x_461, 2, x_412);
lean_ctor_set(x_461, 3, x_460);
lean_ctor_set(x_461, 4, x_459);
lean_ctor_set(x_461, 5, x_390);
lean_ctor_set_uint8(x_461, sizeof(void*)*6, x_415);
lean_ctor_set_uint8(x_461, sizeof(void*)*6 + 1, x_29);
x_462 = lean_apply_6(x_439, x_461, x_2, x_3, x_4, x_5, x_438);
return x_462;
}
default: 
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_440);
x_463 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_404)) {
 x_464 = lean_alloc_ctor(0, 1, 0);
} else {
 x_464 = x_404;
 lean_ctor_set_tag(x_464, 0);
}
lean_ctor_set(x_464, 0, x_437);
x_465 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_466 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_466, 0, x_8);
lean_ctor_set(x_466, 1, x_463);
lean_ctor_set(x_466, 2, x_412);
lean_ctor_set(x_466, 3, x_465);
lean_ctor_set(x_466, 4, x_464);
lean_ctor_set(x_466, 5, x_390);
lean_ctor_set_uint8(x_466, sizeof(void*)*6, x_415);
lean_ctor_set_uint8(x_466, sizeof(void*)*6 + 1, x_29);
x_467 = lean_apply_6(x_439, x_466, x_2, x_3, x_4, x_5, x_438);
return x_467;
}
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_468 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_404)) {
 x_469 = lean_alloc_ctor(0, 1, 0);
} else {
 x_469 = x_404;
 lean_ctor_set_tag(x_469, 0);
}
lean_ctor_set(x_469, 0, x_437);
x_470 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_471 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_471, 0, x_8);
lean_ctor_set(x_471, 1, x_468);
lean_ctor_set(x_471, 2, x_412);
lean_ctor_set(x_471, 3, x_470);
lean_ctor_set(x_471, 4, x_469);
lean_ctor_set(x_471, 5, x_390);
lean_ctor_set_uint8(x_471, sizeof(void*)*6, x_415);
lean_ctor_set_uint8(x_471, sizeof(void*)*6 + 1, x_29);
x_472 = lean_apply_6(x_439, x_471, x_2, x_3, x_4, x_5, x_438);
return x_472;
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_412);
lean_dec(x_404);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_473 = lean_ctor_get(x_436, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_436, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_475 = x_436;
} else {
 lean_dec_ref(x_436);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
return x_476;
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_404);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_477 = lean_ctor_get(x_431, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_431, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_479 = x_431;
} else {
 lean_dec_ref(x_431);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_478);
return x_480;
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_404);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_481 = lean_ctor_get(x_428, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_428, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_483 = x_428;
} else {
 lean_dec_ref(x_428);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
return x_484;
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_404);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_485 = lean_ctor_get(x_425, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_425, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_487 = x_425;
} else {
 lean_dec_ref(x_425);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_404);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_489 = lean_ctor_get(x_421, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_421, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_491 = x_421;
} else {
 lean_dec_ref(x_421);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_404);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_493 = lean_ctor_get(x_416, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_416, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_495 = x_416;
} else {
 lean_dec_ref(x_416);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_408);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_497 = lean_ctor_get(x_411, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_411, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_499 = x_411;
} else {
 lean_dec_ref(x_411);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_27);
x_501 = l_Lean_ConstantInfo_type(x_28);
x_502 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_503 = lean_st_mk_ref(x_502, x_385);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_504);
x_507 = l_Lean_Compiler_LCNF_toLCNFType(x_501, x_506, x_504, x_4, x_5, x_505);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = lean_st_ref_get(x_504, x_509);
lean_dec(x_504);
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_512 = x_510;
} else {
 lean_dec_ref(x_510);
 x_512 = lean_box(0);
}
x_513 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_508);
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_508);
lean_ctor_set(x_514, 1, x_513);
x_515 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_514, x_2, x_3, x_4, x_5, x_511);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_518 = x_515;
} else {
 lean_dec_ref(x_515);
 x_518 = lean_box(0);
}
x_519 = lean_ctor_get(x_516, 1);
lean_inc(x_519);
lean_dec(x_516);
x_520 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
x_521 = l_Lean_Compiler_LCNF_toDecl___closed__12;
x_522 = 0;
x_523 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_523, 0, x_8);
lean_ctor_set(x_523, 1, x_520);
lean_ctor_set(x_523, 2, x_508);
lean_ctor_set(x_523, 3, x_519);
lean_ctor_set(x_523, 4, x_521);
lean_ctor_set(x_523, 5, x_390);
lean_ctor_set_uint8(x_523, sizeof(void*)*6, x_522);
lean_ctor_set_uint8(x_523, sizeof(void*)*6 + 1, x_29);
if (lean_is_scalar(x_518)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_518;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_517);
return x_524;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_504);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_525 = lean_ctor_get(x_507, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_507, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_527 = x_507;
} else {
 lean_dec_ref(x_507);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_386);
lean_dec(x_27);
x_529 = lean_ctor_get(x_393, 0);
lean_inc(x_529);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_530 = x_393;
} else {
 lean_dec_ref(x_393);
 x_530 = lean_box(0);
}
x_531 = l_Lean_ConstantInfo_type(x_28);
x_532 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_533 = lean_st_mk_ref(x_532, x_385);
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_536 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_534);
x_537 = l_Lean_Compiler_LCNF_toLCNFType(x_531, x_536, x_534, x_4, x_5, x_535);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; lean_object* x_553; lean_object* x_554; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_st_ref_get(x_534, x_539);
lean_dec(x_534);
x_541 = lean_ctor_get(x_540, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_542 = x_540;
} else {
 lean_dec_ref(x_540);
 x_542 = lean_box(0);
}
x_543 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_538);
if (lean_is_scalar(x_542)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_542;
}
lean_ctor_set(x_544, 0, x_538);
lean_ctor_set(x_544, 1, x_543);
x_545 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_544, x_2, x_3, x_4, x_5, x_541);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_548 = x_545;
} else {
 lean_dec_ref(x_545);
 x_548 = lean_box(0);
}
x_549 = lean_ctor_get(x_546, 1);
lean_inc(x_549);
lean_dec(x_546);
x_550 = l_Lean_ConstantInfo_levelParams(x_28);
lean_dec(x_28);
if (lean_is_scalar(x_530)) {
 x_551 = lean_alloc_ctor(1, 1, 0);
} else {
 x_551 = x_530;
}
lean_ctor_set(x_551, 0, x_529);
x_552 = 0;
x_553 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_553, 0, x_8);
lean_ctor_set(x_553, 1, x_550);
lean_ctor_set(x_553, 2, x_538);
lean_ctor_set(x_553, 3, x_549);
lean_ctor_set(x_553, 4, x_551);
lean_ctor_set(x_553, 5, x_390);
lean_ctor_set_uint8(x_553, sizeof(void*)*6, x_552);
lean_ctor_set_uint8(x_553, sizeof(void*)*6 + 1, x_29);
if (lean_is_scalar(x_548)) {
 x_554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_554 = x_548;
}
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_547);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_534);
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_390);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_555 = lean_ctor_get(x_537, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_537, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_557 = x_537;
} else {
 lean_dec_ref(x_537);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(1, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_556);
return x_558;
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
