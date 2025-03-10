// Lean compiler output
// Module: Lean.Compiler.LCNF.ToDecl
// Imports: Lean.Meta.Transform Lean.Meta.Match.MatcherInfo Lean.Compiler.ExternAttr Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.ToLCNF
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__1(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_inlineAttrs;
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Name_str___override(x_1, x_9);
lean_inc(x_8);
x_11 = l_Lean_Environment_find_x3f(x_8, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Environment_find_x3f(x_8, x_1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___closed__1;
lean_inc(x_1);
x_20 = l_Lean_Name_str___override(x_1, x_19);
lean_inc(x_18);
x_21 = l_Lean_Environment_find_x3f(x_18, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Environment_find_x3f(x_18, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_1);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
return x_27;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_is_unsafe_rec_name(x_1);
if (lean_obj_tag(x_7) == 0)
{
x_8 = x_1;
goto block_637;
}
else
{
lean_object* x_638; 
lean_dec(x_1);
x_638 = lean_ctor_get(x_7, 0);
lean_inc(x_638);
lean_dec(x_7);
x_8 = x_638;
goto block_637;
}
block_637:
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_632; 
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_632 = l_Lean_ConstantInfo_isPartial(x_27);
if (x_632 == 0)
{
uint8_t x_633; 
x_633 = l_Lean_ConstantInfo_isUnsafe(x_27);
if (x_633 == 0)
{
uint8_t x_634; 
x_634 = 1;
x_28 = x_634;
goto block_631;
}
else
{
uint8_t x_635; 
x_635 = 0;
x_28 = x_635;
goto block_631;
}
}
else
{
uint8_t x_636; 
x_636 = 0;
x_28 = x_636;
goto block_631;
}
block_631:
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
x_45 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_43, x_44, x_42, x_8);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; lean_object* x_47; 
x_46 = 1;
lean_inc(x_27);
x_47 = l_Lean_ConstantInfo_value_x3f(x_27, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_27);
x_48 = l_Lean_MessageData_ofName(x_8);
x_49 = l_Lean_Compiler_LCNF_toDecl___closed__2;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_48);
lean_ctor_set(x_38, 0, x_49);
x_50 = l_Lean_Compiler_LCNF_toDecl___closed__8;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_50);
lean_ctor_set(x_29, 0, x_38);
x_51 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_29, x_2, x_3, x_4, x_5, x_41);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
uint8_t x_52; 
lean_free_object(x_38);
lean_free_object(x_29);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = l_Lean_ConstantInfo_type(x_27);
x_55 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_56 = lean_st_mk_ref(x_55, x_41);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_57);
x_60 = l_Lean_Compiler_LCNF_toLCNFType(x_54, x_59, x_57, x_4, x_5, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_64 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_57);
x_65 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_53, x_63, x_64, x_59, x_57, x_4, x_5, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_69 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_66, x_68, x_69, x_4, x_5, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_71, x_73, x_69, x_4, x_5, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_5);
lean_inc(x_4);
x_77 = l_Lean_Compiler_LCNF_inlineMatchers(x_75, x_4, x_5, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_5);
lean_inc(x_4);
x_80 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_78, x_73, x_69, x_4, x_5, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_57, x_82);
lean_dec(x_57);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_81, x_2, x_3, x_4, x_5, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_86) == 1)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
switch (lean_obj_tag(x_89)) {
case 4:
{
uint8_t x_90; 
lean_free_object(x_47);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
x_92 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_89, 0);
lean_ctor_set(x_89, 0, x_86);
x_93 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_94 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_94, 0, x_8);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_61);
lean_ctor_set(x_94, 3, x_93);
lean_ctor_set(x_94, 4, x_89);
lean_ctor_set(x_94, 5, x_37);
lean_ctor_set_uint8(x_94, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_94, sizeof(void*)*6 + 1, x_28);
x_95 = lean_apply_6(x_88, x_94, x_2, x_3, x_4, x_5, x_87);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_89);
x_96 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_86);
x_98 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_99 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_99, 0, x_8);
lean_ctor_set(x_99, 1, x_96);
lean_ctor_set(x_99, 2, x_61);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set(x_99, 4, x_97);
lean_ctor_set(x_99, 5, x_37);
lean_ctor_set_uint8(x_99, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_99, sizeof(void*)*6 + 1, x_28);
x_100 = lean_apply_6(x_88, x_99, x_2, x_3, x_4, x_5, x_87);
return x_100;
}
}
case 5:
{
uint8_t x_101; 
lean_free_object(x_47);
x_101 = !lean_is_exclusive(x_89);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_89, 0);
lean_dec(x_102);
x_103 = lean_ctor_get(x_86, 0);
lean_inc(x_103);
lean_dec(x_86);
x_104 = l_Lean_Compiler_LCNF_eraseFunDecl(x_103, x_64, x_2, x_3, x_4, x_5, x_87);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_107 = lean_ctor_get(x_103, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
lean_dec(x_103);
lean_ctor_set_tag(x_89, 0);
lean_ctor_set(x_89, 0, x_108);
x_109 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_109, 0, x_8);
lean_ctor_set(x_109, 1, x_106);
lean_ctor_set(x_109, 2, x_61);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set(x_109, 4, x_89);
lean_ctor_set(x_109, 5, x_37);
lean_ctor_set_uint8(x_109, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_109, sizeof(void*)*6 + 1, x_28);
x_110 = lean_apply_6(x_88, x_109, x_2, x_3, x_4, x_5, x_105);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_89);
x_111 = lean_ctor_get(x_86, 0);
lean_inc(x_111);
lean_dec(x_86);
x_112 = l_Lean_Compiler_LCNF_eraseFunDecl(x_111, x_64, x_2, x_3, x_4, x_5, x_87);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_115 = lean_ctor_get(x_111, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 4);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_118, 0, x_8);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 2, x_61);
lean_ctor_set(x_118, 3, x_115);
lean_ctor_set(x_118, 4, x_117);
lean_ctor_set(x_118, 5, x_37);
lean_ctor_set_uint8(x_118, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_118, sizeof(void*)*6 + 1, x_28);
x_119 = lean_apply_6(x_88, x_118, x_2, x_3, x_4, x_5, x_113);
return x_119;
}
}
case 6:
{
uint8_t x_120; 
lean_free_object(x_47);
x_120 = !lean_is_exclusive(x_89);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_89, 0);
lean_dec(x_121);
x_122 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_89, 0);
lean_ctor_set(x_89, 0, x_86);
x_123 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_124 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_124, 0, x_8);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_61);
lean_ctor_set(x_124, 3, x_123);
lean_ctor_set(x_124, 4, x_89);
lean_ctor_set(x_124, 5, x_37);
lean_ctor_set_uint8(x_124, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_124, sizeof(void*)*6 + 1, x_28);
x_125 = lean_apply_6(x_88, x_124, x_2, x_3, x_4, x_5, x_87);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_89);
x_126 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_86);
x_128 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_129 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_129, 0, x_8);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_61);
lean_ctor_set(x_129, 3, x_128);
lean_ctor_set(x_129, 4, x_127);
lean_ctor_set(x_129, 5, x_37);
lean_ctor_set_uint8(x_129, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_129, sizeof(void*)*6 + 1, x_28);
x_130 = lean_apply_6(x_88, x_129, x_2, x_3, x_4, x_5, x_87);
return x_130;
}
}
default: 
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_89);
x_131 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_86);
x_132 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_133 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_133, 0, x_8);
lean_ctor_set(x_133, 1, x_131);
lean_ctor_set(x_133, 2, x_61);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set(x_133, 4, x_47);
lean_ctor_set(x_133, 5, x_37);
lean_ctor_set_uint8(x_133, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_133, sizeof(void*)*6 + 1, x_28);
x_134 = lean_apply_6(x_88, x_133, x_2, x_3, x_4, x_5, x_87);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_86);
x_136 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_137 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_137, 0, x_8);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_61);
lean_ctor_set(x_137, 3, x_136);
lean_ctor_set(x_137, 4, x_47);
lean_ctor_set(x_137, 5, x_37);
lean_ctor_set_uint8(x_137, sizeof(void*)*6, x_64);
lean_ctor_set_uint8(x_137, sizeof(void*)*6 + 1, x_28);
x_138 = lean_apply_6(x_88, x_137, x_2, x_3, x_4, x_5, x_87);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_dec(x_61);
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_85);
if (x_139 == 0)
{
return x_85;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_85, 0);
x_141 = lean_ctor_get(x_85, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_85);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_61);
lean_dec(x_57);
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_80);
if (x_143 == 0)
{
return x_80;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_80, 0);
x_145 = lean_ctor_get(x_80, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_80);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_61);
lean_dec(x_57);
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_77);
if (x_147 == 0)
{
return x_77;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_77, 0);
x_149 = lean_ctor_get(x_77, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_77);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_61);
lean_dec(x_57);
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_151 = !lean_is_exclusive(x_74);
if (x_151 == 0)
{
return x_74;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_74, 0);
x_153 = lean_ctor_get(x_74, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_74);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_61);
lean_dec(x_57);
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_70);
if (x_155 == 0)
{
return x_70;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_70, 0);
x_157 = lean_ctor_get(x_70, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_70);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_61);
lean_dec(x_57);
lean_free_object(x_47);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_65);
if (x_159 == 0)
{
return x_65;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_65, 0);
x_161 = lean_ctor_get(x_65, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_65);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_57);
lean_free_object(x_47);
lean_dec(x_53);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_60);
if (x_163 == 0)
{
return x_60;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_60, 0);
x_165 = lean_ctor_get(x_60, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_60);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_ctor_get(x_47, 0);
lean_inc(x_167);
lean_dec(x_47);
x_168 = l_Lean_ConstantInfo_type(x_27);
x_169 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_170 = lean_st_mk_ref(x_169, x_41);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_171);
x_174 = l_Lean_Compiler_LCNF_toLCNFType(x_168, x_173, x_171, x_4, x_5, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_178 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_171);
x_179 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_167, x_177, x_178, x_173, x_171, x_4, x_5, x_176);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_183 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_184 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_180, x_182, x_183, x_4, x_5, x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_188 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_185, x_187, x_183, x_4, x_5, x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
lean_inc(x_5);
lean_inc(x_4);
x_191 = l_Lean_Compiler_LCNF_inlineMatchers(x_189, x_4, x_5, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_5);
lean_inc(x_4);
x_194 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_192, x_187, x_183, x_4, x_5, x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_st_ref_get(x_171, x_196);
lean_dec(x_171);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_199 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_195, x_2, x_3, x_4, x_5, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_200) == 1)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
switch (lean_obj_tag(x_203)) {
case 4:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_204 = x_203;
} else {
 lean_dec_ref(x_203);
 x_204 = lean_box(0);
}
x_205 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 1, 0);
} else {
 x_206 = x_204;
 lean_ctor_set_tag(x_206, 0);
}
lean_ctor_set(x_206, 0, x_200);
x_207 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_208 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_208, 0, x_8);
lean_ctor_set(x_208, 1, x_205);
lean_ctor_set(x_208, 2, x_175);
lean_ctor_set(x_208, 3, x_207);
lean_ctor_set(x_208, 4, x_206);
lean_ctor_set(x_208, 5, x_37);
lean_ctor_set_uint8(x_208, sizeof(void*)*6, x_178);
lean_ctor_set_uint8(x_208, sizeof(void*)*6 + 1, x_28);
x_209 = lean_apply_6(x_202, x_208, x_2, x_3, x_4, x_5, x_201);
return x_209;
}
case 5:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_210 = x_203;
} else {
 lean_dec_ref(x_203);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_200, 0);
lean_inc(x_211);
lean_dec(x_200);
x_212 = l_Lean_Compiler_LCNF_eraseFunDecl(x_211, x_178, x_2, x_3, x_4, x_5, x_201);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_215 = lean_ctor_get(x_211, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_211, 4);
lean_inc(x_216);
lean_dec(x_211);
if (lean_is_scalar(x_210)) {
 x_217 = lean_alloc_ctor(0, 1, 0);
} else {
 x_217 = x_210;
 lean_ctor_set_tag(x_217, 0);
}
lean_ctor_set(x_217, 0, x_216);
x_218 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_218, 0, x_8);
lean_ctor_set(x_218, 1, x_214);
lean_ctor_set(x_218, 2, x_175);
lean_ctor_set(x_218, 3, x_215);
lean_ctor_set(x_218, 4, x_217);
lean_ctor_set(x_218, 5, x_37);
lean_ctor_set_uint8(x_218, sizeof(void*)*6, x_178);
lean_ctor_set_uint8(x_218, sizeof(void*)*6 + 1, x_28);
x_219 = lean_apply_6(x_202, x_218, x_2, x_3, x_4, x_5, x_213);
return x_219;
}
case 6:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_220 = x_203;
} else {
 lean_dec_ref(x_203);
 x_220 = lean_box(0);
}
x_221 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 1, 0);
} else {
 x_222 = x_220;
 lean_ctor_set_tag(x_222, 0);
}
lean_ctor_set(x_222, 0, x_200);
x_223 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_224 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_224, 0, x_8);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_175);
lean_ctor_set(x_224, 3, x_223);
lean_ctor_set(x_224, 4, x_222);
lean_ctor_set(x_224, 5, x_37);
lean_ctor_set_uint8(x_224, sizeof(void*)*6, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*6 + 1, x_28);
x_225 = lean_apply_6(x_202, x_224, x_2, x_3, x_4, x_5, x_201);
return x_225;
}
default: 
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_203);
x_226 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_200);
x_228 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_229 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_229, 0, x_8);
lean_ctor_set(x_229, 1, x_226);
lean_ctor_set(x_229, 2, x_175);
lean_ctor_set(x_229, 3, x_228);
lean_ctor_set(x_229, 4, x_227);
lean_ctor_set(x_229, 5, x_37);
lean_ctor_set_uint8(x_229, sizeof(void*)*6, x_178);
lean_ctor_set_uint8(x_229, sizeof(void*)*6 + 1, x_28);
x_230 = lean_apply_6(x_202, x_229, x_2, x_3, x_4, x_5, x_201);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_200);
x_233 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_234 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_234, 0, x_8);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_175);
lean_ctor_set(x_234, 3, x_233);
lean_ctor_set(x_234, 4, x_232);
lean_ctor_set(x_234, 5, x_37);
lean_ctor_set_uint8(x_234, sizeof(void*)*6, x_178);
lean_ctor_set_uint8(x_234, sizeof(void*)*6 + 1, x_28);
x_235 = lean_apply_6(x_202, x_234, x_2, x_3, x_4, x_5, x_201);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_175);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_236 = lean_ctor_get(x_199, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_199, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_238 = x_199;
} else {
 lean_dec_ref(x_199);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_240 = lean_ctor_get(x_194, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_194, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_242 = x_194;
} else {
 lean_dec_ref(x_194);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_244 = lean_ctor_get(x_191, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_191, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_246 = x_191;
} else {
 lean_dec_ref(x_191);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_248 = lean_ctor_get(x_188, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_188, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_250 = x_188;
} else {
 lean_dec_ref(x_188);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_252 = lean_ctor_get(x_184, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_184, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_254 = x_184;
} else {
 lean_dec_ref(x_184);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_256 = lean_ctor_get(x_179, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_179, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_258 = x_179;
} else {
 lean_dec_ref(x_179);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_171);
lean_dec(x_167);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_260 = lean_ctor_get(x_174, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_174, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_262 = x_174;
} else {
 lean_dec_ref(x_174);
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
}
else
{
uint8_t x_264; 
lean_free_object(x_38);
lean_free_object(x_29);
x_264 = !lean_is_exclusive(x_45);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_265 = lean_ctor_get(x_45, 0);
x_266 = l_Lean_ConstantInfo_type(x_27);
x_267 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_268 = lean_st_mk_ref(x_267, x_41);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_269);
x_272 = l_Lean_Compiler_LCNF_toLCNFType(x_266, x_271, x_269, x_4, x_5, x_270);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_st_ref_get(x_269, x_274);
lean_dec(x_269);
x_276 = !lean_is_exclusive(x_275);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_275, 1);
x_278 = lean_ctor_get(x_275, 0);
lean_dec(x_278);
x_279 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_273);
lean_ctor_set(x_275, 1, x_279);
lean_ctor_set(x_275, 0, x_273);
x_280 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_275, x_2, x_3, x_4, x_5, x_277);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_285 = 0;
x_286 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_286, 0, x_8);
lean_ctor_set(x_286, 1, x_284);
lean_ctor_set(x_286, 2, x_273);
lean_ctor_set(x_286, 3, x_283);
lean_ctor_set(x_286, 4, x_45);
lean_ctor_set(x_286, 5, x_37);
lean_ctor_set_uint8(x_286, sizeof(void*)*6, x_285);
lean_ctor_set_uint8(x_286, sizeof(void*)*6 + 1, x_28);
lean_ctor_set(x_280, 0, x_286);
return x_280;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_280, 0);
x_288 = lean_ctor_get(x_280, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_280);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_291 = 0;
x_292 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_292, 0, x_8);
lean_ctor_set(x_292, 1, x_290);
lean_ctor_set(x_292, 2, x_273);
lean_ctor_set(x_292, 3, x_289);
lean_ctor_set(x_292, 4, x_45);
lean_ctor_set(x_292, 5, x_37);
lean_ctor_set_uint8(x_292, sizeof(void*)*6, x_291);
lean_ctor_set_uint8(x_292, sizeof(void*)*6 + 1, x_28);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_288);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; 
x_294 = lean_ctor_get(x_275, 1);
lean_inc(x_294);
lean_dec(x_275);
x_295 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_273);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_273);
lean_ctor_set(x_296, 1, x_295);
x_297 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_296, x_2, x_3, x_4, x_5, x_294);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_303 = 0;
x_304 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_304, 0, x_8);
lean_ctor_set(x_304, 1, x_302);
lean_ctor_set(x_304, 2, x_273);
lean_ctor_set(x_304, 3, x_301);
lean_ctor_set(x_304, 4, x_45);
lean_ctor_set(x_304, 5, x_37);
lean_ctor_set_uint8(x_304, sizeof(void*)*6, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_300)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_300;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_299);
return x_305;
}
}
else
{
uint8_t x_306; 
lean_dec(x_269);
lean_free_object(x_45);
lean_dec(x_265);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_306 = !lean_is_exclusive(x_272);
if (x_306 == 0)
{
return x_272;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_272, 0);
x_308 = lean_ctor_get(x_272, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_272);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_310 = lean_ctor_get(x_45, 0);
lean_inc(x_310);
lean_dec(x_45);
x_311 = l_Lean_ConstantInfo_type(x_27);
x_312 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_313 = lean_st_mk_ref(x_312, x_41);
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
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_st_ref_get(x_314, x_319);
lean_dec(x_314);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_322 = x_320;
} else {
 lean_dec_ref(x_320);
 x_322 = lean_box(0);
}
x_323 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_318);
if (lean_is_scalar(x_322)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_322;
}
lean_ctor_set(x_324, 0, x_318);
lean_ctor_set(x_324, 1, x_323);
x_325 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_324, x_2, x_3, x_4, x_5, x_321);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
lean_dec(x_326);
x_330 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_331 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_331, 0, x_310);
x_332 = 0;
x_333 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_333, 0, x_8);
lean_ctor_set(x_333, 1, x_330);
lean_ctor_set(x_333, 2, x_318);
lean_ctor_set(x_333, 3, x_329);
lean_ctor_set(x_333, 4, x_331);
lean_ctor_set(x_333, 5, x_37);
lean_ctor_set_uint8(x_333, sizeof(void*)*6, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_328)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_328;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_327);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_314);
lean_dec(x_310);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_335 = lean_ctor_get(x_317, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_317, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_337 = x_317;
} else {
 lean_dec_ref(x_317);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_339 = lean_ctor_get(x_38, 0);
x_340 = lean_ctor_get(x_38, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_38);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
lean_dec(x_339);
x_342 = l_Lean_instInhabitedExternAttrData;
x_343 = l_Lean_Compiler_LCNF_toDecl___closed__6;
lean_inc(x_8);
x_344 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_342, x_343, x_341, x_8);
if (lean_obj_tag(x_344) == 0)
{
uint8_t x_345; lean_object* x_346; 
x_345 = 1;
lean_inc(x_27);
x_346 = l_Lean_ConstantInfo_value_x3f(x_27, x_345);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_37);
lean_dec(x_27);
x_347 = l_Lean_MessageData_ofName(x_8);
x_348 = l_Lean_Compiler_LCNF_toDecl___closed__2;
x_349 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_347);
x_350 = l_Lean_Compiler_LCNF_toDecl___closed__8;
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_350);
lean_ctor_set(x_29, 0, x_349);
x_351 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_29, x_2, x_3, x_4, x_5, x_340);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_free_object(x_29);
x_352 = lean_ctor_get(x_346, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_353 = x_346;
} else {
 lean_dec_ref(x_346);
 x_353 = lean_box(0);
}
x_354 = l_Lean_ConstantInfo_type(x_27);
x_355 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_356 = lean_st_mk_ref(x_355, x_340);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_357);
x_360 = l_Lean_Compiler_LCNF_toLCNFType(x_354, x_359, x_357, x_4, x_5, x_358);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_364 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_357);
x_365 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_352, x_363, x_364, x_359, x_357, x_4, x_5, x_362);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_369 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_370 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_366, x_368, x_369, x_4, x_5, x_367);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_374 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_371, x_373, x_369, x_4, x_5, x_372);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
lean_inc(x_5);
lean_inc(x_4);
x_377 = l_Lean_Compiler_LCNF_inlineMatchers(x_375, x_4, x_5, x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
lean_inc(x_5);
lean_inc(x_4);
x_380 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_378, x_373, x_369, x_4, x_5, x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_st_ref_get(x_357, x_382);
lean_dec(x_357);
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec(x_383);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_385 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_381, x_2, x_3, x_4, x_5, x_384);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_386) == 1)
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_386, 1);
lean_inc(x_389);
switch (lean_obj_tag(x_389)) {
case 4:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_353);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_390 = x_389;
} else {
 lean_dec_ref(x_389);
 x_390 = lean_box(0);
}
x_391 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(0, 1, 0);
} else {
 x_392 = x_390;
 lean_ctor_set_tag(x_392, 0);
}
lean_ctor_set(x_392, 0, x_386);
x_393 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_394 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_394, 0, x_8);
lean_ctor_set(x_394, 1, x_391);
lean_ctor_set(x_394, 2, x_361);
lean_ctor_set(x_394, 3, x_393);
lean_ctor_set(x_394, 4, x_392);
lean_ctor_set(x_394, 5, x_37);
lean_ctor_set_uint8(x_394, sizeof(void*)*6, x_364);
lean_ctor_set_uint8(x_394, sizeof(void*)*6 + 1, x_28);
x_395 = lean_apply_6(x_388, x_394, x_2, x_3, x_4, x_5, x_387);
return x_395;
}
case 5:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_353);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_396 = x_389;
} else {
 lean_dec_ref(x_389);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_386, 0);
lean_inc(x_397);
lean_dec(x_386);
x_398 = l_Lean_Compiler_LCNF_eraseFunDecl(x_397, x_364, x_2, x_3, x_4, x_5, x_387);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_400 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_401 = lean_ctor_get(x_397, 2);
lean_inc(x_401);
x_402 = lean_ctor_get(x_397, 4);
lean_inc(x_402);
lean_dec(x_397);
if (lean_is_scalar(x_396)) {
 x_403 = lean_alloc_ctor(0, 1, 0);
} else {
 x_403 = x_396;
 lean_ctor_set_tag(x_403, 0);
}
lean_ctor_set(x_403, 0, x_402);
x_404 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_404, 0, x_8);
lean_ctor_set(x_404, 1, x_400);
lean_ctor_set(x_404, 2, x_361);
lean_ctor_set(x_404, 3, x_401);
lean_ctor_set(x_404, 4, x_403);
lean_ctor_set(x_404, 5, x_37);
lean_ctor_set_uint8(x_404, sizeof(void*)*6, x_364);
lean_ctor_set_uint8(x_404, sizeof(void*)*6 + 1, x_28);
x_405 = lean_apply_6(x_388, x_404, x_2, x_3, x_4, x_5, x_399);
return x_405;
}
case 6:
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_353);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_406 = x_389;
} else {
 lean_dec_ref(x_389);
 x_406 = lean_box(0);
}
x_407 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_406)) {
 x_408 = lean_alloc_ctor(0, 1, 0);
} else {
 x_408 = x_406;
 lean_ctor_set_tag(x_408, 0);
}
lean_ctor_set(x_408, 0, x_386);
x_409 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_410 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_410, 0, x_8);
lean_ctor_set(x_410, 1, x_407);
lean_ctor_set(x_410, 2, x_361);
lean_ctor_set(x_410, 3, x_409);
lean_ctor_set(x_410, 4, x_408);
lean_ctor_set(x_410, 5, x_37);
lean_ctor_set_uint8(x_410, sizeof(void*)*6, x_364);
lean_ctor_set_uint8(x_410, sizeof(void*)*6 + 1, x_28);
x_411 = lean_apply_6(x_388, x_410, x_2, x_3, x_4, x_5, x_387);
return x_411;
}
default: 
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_389);
x_412 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_353)) {
 x_413 = lean_alloc_ctor(0, 1, 0);
} else {
 x_413 = x_353;
 lean_ctor_set_tag(x_413, 0);
}
lean_ctor_set(x_413, 0, x_386);
x_414 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_415 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_415, 0, x_8);
lean_ctor_set(x_415, 1, x_412);
lean_ctor_set(x_415, 2, x_361);
lean_ctor_set(x_415, 3, x_414);
lean_ctor_set(x_415, 4, x_413);
lean_ctor_set(x_415, 5, x_37);
lean_ctor_set_uint8(x_415, sizeof(void*)*6, x_364);
lean_ctor_set_uint8(x_415, sizeof(void*)*6 + 1, x_28);
x_416 = lean_apply_6(x_388, x_415, x_2, x_3, x_4, x_5, x_387);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_417 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_353)) {
 x_418 = lean_alloc_ctor(0, 1, 0);
} else {
 x_418 = x_353;
 lean_ctor_set_tag(x_418, 0);
}
lean_ctor_set(x_418, 0, x_386);
x_419 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_420 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_420, 0, x_8);
lean_ctor_set(x_420, 1, x_417);
lean_ctor_set(x_420, 2, x_361);
lean_ctor_set(x_420, 3, x_419);
lean_ctor_set(x_420, 4, x_418);
lean_ctor_set(x_420, 5, x_37);
lean_ctor_set_uint8(x_420, sizeof(void*)*6, x_364);
lean_ctor_set_uint8(x_420, sizeof(void*)*6 + 1, x_28);
x_421 = lean_apply_6(x_388, x_420, x_2, x_3, x_4, x_5, x_387);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_361);
lean_dec(x_353);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_422 = lean_ctor_get(x_385, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_385, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 lean_ctor_release(x_385, 1);
 x_424 = x_385;
} else {
 lean_dec_ref(x_385);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_361);
lean_dec(x_357);
lean_dec(x_353);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_426 = lean_ctor_get(x_380, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_380, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_428 = x_380;
} else {
 lean_dec_ref(x_380);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_361);
lean_dec(x_357);
lean_dec(x_353);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_430 = lean_ctor_get(x_377, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_377, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_432 = x_377;
} else {
 lean_dec_ref(x_377);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_361);
lean_dec(x_357);
lean_dec(x_353);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_434 = lean_ctor_get(x_374, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_374, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_436 = x_374;
} else {
 lean_dec_ref(x_374);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_361);
lean_dec(x_357);
lean_dec(x_353);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_438 = lean_ctor_get(x_370, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_370, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_440 = x_370;
} else {
 lean_dec_ref(x_370);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_361);
lean_dec(x_357);
lean_dec(x_353);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_442 = lean_ctor_get(x_365, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_365, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_444 = x_365;
} else {
 lean_dec_ref(x_365);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_357);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_446 = lean_ctor_get(x_360, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_360, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_448 = x_360;
} else {
 lean_dec_ref(x_360);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_free_object(x_29);
x_450 = lean_ctor_get(x_344, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_451 = x_344;
} else {
 lean_dec_ref(x_344);
 x_451 = lean_box(0);
}
x_452 = l_Lean_ConstantInfo_type(x_27);
x_453 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_454 = lean_st_mk_ref(x_453, x_340);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
x_457 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_455);
x_458 = l_Lean_Compiler_LCNF_toLCNFType(x_452, x_457, x_455, x_4, x_5, x_456);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; lean_object* x_475; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_st_ref_get(x_455, x_460);
lean_dec(x_455);
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
x_464 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_459);
if (lean_is_scalar(x_463)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_463;
}
lean_ctor_set(x_465, 0, x_459);
lean_ctor_set(x_465, 1, x_464);
x_466 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_465, x_2, x_3, x_4, x_5, x_462);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_469 = x_466;
} else {
 lean_dec_ref(x_466);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec(x_467);
x_471 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_451)) {
 x_472 = lean_alloc_ctor(1, 1, 0);
} else {
 x_472 = x_451;
}
lean_ctor_set(x_472, 0, x_450);
x_473 = 0;
x_474 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_474, 0, x_8);
lean_ctor_set(x_474, 1, x_471);
lean_ctor_set(x_474, 2, x_459);
lean_ctor_set(x_474, 3, x_470);
lean_ctor_set(x_474, 4, x_472);
lean_ctor_set(x_474, 5, x_37);
lean_ctor_set_uint8(x_474, sizeof(void*)*6, x_473);
lean_ctor_set_uint8(x_474, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_469)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_469;
}
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_468);
return x_475;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_455);
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_476 = lean_ctor_get(x_458, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_458, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_478 = x_458;
} else {
 lean_dec_ref(x_458);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_480 = lean_ctor_get(x_29, 0);
x_481 = lean_ctor_get(x_29, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_29);
x_482 = lean_ctor_get(x_480, 0);
lean_inc(x_482);
lean_dec(x_480);
x_483 = l_Lean_Compiler_instInhabitedInlineAttributeKind;
x_484 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_485 = lean_box(x_483);
lean_inc(x_8);
x_486 = l_Lean_EnumAttributes_getValue___rarg(x_485, x_484, x_482, x_8);
x_487 = lean_st_ref_get(x_5, x_481);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_490 = x_487;
} else {
 lean_dec_ref(x_487);
 x_490 = lean_box(0);
}
x_491 = lean_ctor_get(x_488, 0);
lean_inc(x_491);
lean_dec(x_488);
x_492 = l_Lean_instInhabitedExternAttrData;
x_493 = l_Lean_Compiler_LCNF_toDecl___closed__6;
lean_inc(x_8);
x_494 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_492, x_493, x_491, x_8);
if (lean_obj_tag(x_494) == 0)
{
uint8_t x_495; lean_object* x_496; 
x_495 = 1;
lean_inc(x_27);
x_496 = l_Lean_ConstantInfo_value_x3f(x_27, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_486);
lean_dec(x_27);
x_497 = l_Lean_MessageData_ofName(x_8);
x_498 = l_Lean_Compiler_LCNF_toDecl___closed__2;
if (lean_is_scalar(x_490)) {
 x_499 = lean_alloc_ctor(7, 2, 0);
} else {
 x_499 = x_490;
 lean_ctor_set_tag(x_499, 7);
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_497);
x_500 = l_Lean_Compiler_LCNF_toDecl___closed__8;
x_501 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
x_502 = l_Lean_throwError___at_Lean_Compiler_LCNF_toDecl___spec__1(x_501, x_2, x_3, x_4, x_5, x_489);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_490);
x_503 = lean_ctor_get(x_496, 0);
lean_inc(x_503);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 x_504 = x_496;
} else {
 lean_dec_ref(x_496);
 x_504 = lean_box(0);
}
x_505 = l_Lean_ConstantInfo_type(x_27);
x_506 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_507 = lean_st_mk_ref(x_506, x_489);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_508);
x_511 = l_Lean_Compiler_LCNF_toLCNFType(x_505, x_510, x_508, x_4, x_5, x_509);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = l_Lean_Compiler_LCNF_toDecl___closed__9;
x_515 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_508);
x_516 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___spec__2___rarg(x_503, x_514, x_515, x_510, x_508, x_4, x_5, x_513);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_519 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__1;
x_520 = l_Lean_Compiler_LCNF_macroInline___closed__2;
lean_inc(x_5);
lean_inc(x_4);
x_521 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_517, x_519, x_520, x_4, x_5, x_518);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = l_Lean_Compiler_LCNF_macroInline___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_525 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_522, x_524, x_520, x_4, x_5, x_523);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
lean_inc(x_5);
lean_inc(x_4);
x_528 = l_Lean_Compiler_LCNF_inlineMatchers(x_526, x_4, x_5, x_527);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
lean_inc(x_5);
lean_inc(x_4);
x_531 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_529, x_524, x_520, x_4, x_5, x_530);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_st_ref_get(x_508, x_533);
lean_dec(x_508);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_536 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_532, x_2, x_3, x_4, x_5, x_535);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = l_Lean_Compiler_LCNF_toDecl___closed__10;
if (lean_obj_tag(x_537) == 1)
{
lean_object* x_540; 
x_540 = lean_ctor_get(x_537, 1);
lean_inc(x_540);
switch (lean_obj_tag(x_540)) {
case 4:
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_504);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 x_541 = x_540;
} else {
 lean_dec_ref(x_540);
 x_541 = lean_box(0);
}
x_542 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_541)) {
 x_543 = lean_alloc_ctor(0, 1, 0);
} else {
 x_543 = x_541;
 lean_ctor_set_tag(x_543, 0);
}
lean_ctor_set(x_543, 0, x_537);
x_544 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_545 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_545, 0, x_8);
lean_ctor_set(x_545, 1, x_542);
lean_ctor_set(x_545, 2, x_512);
lean_ctor_set(x_545, 3, x_544);
lean_ctor_set(x_545, 4, x_543);
lean_ctor_set(x_545, 5, x_486);
lean_ctor_set_uint8(x_545, sizeof(void*)*6, x_515);
lean_ctor_set_uint8(x_545, sizeof(void*)*6 + 1, x_28);
x_546 = lean_apply_6(x_539, x_545, x_2, x_3, x_4, x_5, x_538);
return x_546;
}
case 5:
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_504);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 x_547 = x_540;
} else {
 lean_dec_ref(x_540);
 x_547 = lean_box(0);
}
x_548 = lean_ctor_get(x_537, 0);
lean_inc(x_548);
lean_dec(x_537);
x_549 = l_Lean_Compiler_LCNF_eraseFunDecl(x_548, x_515, x_2, x_3, x_4, x_5, x_538);
x_550 = lean_ctor_get(x_549, 1);
lean_inc(x_550);
lean_dec(x_549);
x_551 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_552 = lean_ctor_get(x_548, 2);
lean_inc(x_552);
x_553 = lean_ctor_get(x_548, 4);
lean_inc(x_553);
lean_dec(x_548);
if (lean_is_scalar(x_547)) {
 x_554 = lean_alloc_ctor(0, 1, 0);
} else {
 x_554 = x_547;
 lean_ctor_set_tag(x_554, 0);
}
lean_ctor_set(x_554, 0, x_553);
x_555 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_555, 0, x_8);
lean_ctor_set(x_555, 1, x_551);
lean_ctor_set(x_555, 2, x_512);
lean_ctor_set(x_555, 3, x_552);
lean_ctor_set(x_555, 4, x_554);
lean_ctor_set(x_555, 5, x_486);
lean_ctor_set_uint8(x_555, sizeof(void*)*6, x_515);
lean_ctor_set_uint8(x_555, sizeof(void*)*6 + 1, x_28);
x_556 = lean_apply_6(x_539, x_555, x_2, x_3, x_4, x_5, x_550);
return x_556;
}
case 6:
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_504);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 x_557 = x_540;
} else {
 lean_dec_ref(x_540);
 x_557 = lean_box(0);
}
x_558 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_557)) {
 x_559 = lean_alloc_ctor(0, 1, 0);
} else {
 x_559 = x_557;
 lean_ctor_set_tag(x_559, 0);
}
lean_ctor_set(x_559, 0, x_537);
x_560 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_561 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_561, 0, x_8);
lean_ctor_set(x_561, 1, x_558);
lean_ctor_set(x_561, 2, x_512);
lean_ctor_set(x_561, 3, x_560);
lean_ctor_set(x_561, 4, x_559);
lean_ctor_set(x_561, 5, x_486);
lean_ctor_set_uint8(x_561, sizeof(void*)*6, x_515);
lean_ctor_set_uint8(x_561, sizeof(void*)*6 + 1, x_28);
x_562 = lean_apply_6(x_539, x_561, x_2, x_3, x_4, x_5, x_538);
return x_562;
}
default: 
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_540);
x_563 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_504)) {
 x_564 = lean_alloc_ctor(0, 1, 0);
} else {
 x_564 = x_504;
 lean_ctor_set_tag(x_564, 0);
}
lean_ctor_set(x_564, 0, x_537);
x_565 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_566 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_566, 0, x_8);
lean_ctor_set(x_566, 1, x_563);
lean_ctor_set(x_566, 2, x_512);
lean_ctor_set(x_566, 3, x_565);
lean_ctor_set(x_566, 4, x_564);
lean_ctor_set(x_566, 5, x_486);
lean_ctor_set_uint8(x_566, sizeof(void*)*6, x_515);
lean_ctor_set_uint8(x_566, sizeof(void*)*6 + 1, x_28);
x_567 = lean_apply_6(x_539, x_566, x_2, x_3, x_4, x_5, x_538);
return x_567;
}
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_504)) {
 x_569 = lean_alloc_ctor(0, 1, 0);
} else {
 x_569 = x_504;
 lean_ctor_set_tag(x_569, 0);
}
lean_ctor_set(x_569, 0, x_537);
x_570 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
x_571 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_571, 0, x_8);
lean_ctor_set(x_571, 1, x_568);
lean_ctor_set(x_571, 2, x_512);
lean_ctor_set(x_571, 3, x_570);
lean_ctor_set(x_571, 4, x_569);
lean_ctor_set(x_571, 5, x_486);
lean_ctor_set_uint8(x_571, sizeof(void*)*6, x_515);
lean_ctor_set_uint8(x_571, sizeof(void*)*6 + 1, x_28);
x_572 = lean_apply_6(x_539, x_571, x_2, x_3, x_4, x_5, x_538);
return x_572;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_512);
lean_dec(x_504);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_573 = lean_ctor_get(x_536, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_536, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_575 = x_536;
} else {
 lean_dec_ref(x_536);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(1, 2, 0);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_573);
lean_ctor_set(x_576, 1, x_574);
return x_576;
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_512);
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_577 = lean_ctor_get(x_531, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_531, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_579 = x_531;
} else {
 lean_dec_ref(x_531);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_512);
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_581 = lean_ctor_get(x_528, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_528, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_583 = x_528;
} else {
 lean_dec_ref(x_528);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(1, 2, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_581);
lean_ctor_set(x_584, 1, x_582);
return x_584;
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_512);
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_585 = lean_ctor_get(x_525, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_525, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_587 = x_525;
} else {
 lean_dec_ref(x_525);
 x_587 = lean_box(0);
}
if (lean_is_scalar(x_587)) {
 x_588 = lean_alloc_ctor(1, 2, 0);
} else {
 x_588 = x_587;
}
lean_ctor_set(x_588, 0, x_585);
lean_ctor_set(x_588, 1, x_586);
return x_588;
}
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_512);
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_589 = lean_ctor_get(x_521, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_521, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_591 = x_521;
} else {
 lean_dec_ref(x_521);
 x_591 = lean_box(0);
}
if (lean_is_scalar(x_591)) {
 x_592 = lean_alloc_ctor(1, 2, 0);
} else {
 x_592 = x_591;
}
lean_ctor_set(x_592, 0, x_589);
lean_ctor_set(x_592, 1, x_590);
return x_592;
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_512);
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_593 = lean_ctor_get(x_516, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_516, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_595 = x_516;
} else {
 lean_dec_ref(x_516);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_594);
return x_596;
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_508);
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_597 = lean_ctor_get(x_511, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_511, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_599 = x_511;
} else {
 lean_dec_ref(x_511);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_490);
x_601 = lean_ctor_get(x_494, 0);
lean_inc(x_601);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_602 = x_494;
} else {
 lean_dec_ref(x_494);
 x_602 = lean_box(0);
}
x_603 = l_Lean_ConstantInfo_type(x_27);
x_604 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_605 = lean_st_mk_ref(x_604, x_489);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
x_608 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_606);
x_609 = l_Lean_Compiler_LCNF_toLCNFType(x_603, x_608, x_606, x_4, x_5, x_607);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_st_ref_get(x_606, x_611);
lean_dec(x_606);
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_614 = x_612;
} else {
 lean_dec_ref(x_612);
 x_614 = lean_box(0);
}
x_615 = l_Lean_Compiler_LCNF_inlineMatchers___lambda__2___closed__1;
lean_inc(x_610);
if (lean_is_scalar(x_614)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_614;
}
lean_ctor_set(x_616, 0, x_610);
lean_ctor_set(x_616, 1, x_615);
x_617 = l_Lean_Loop_forIn_loop___at_Lean_Compiler_LCNF_toDecl___spec__2(x_616, x_2, x_3, x_4, x_5, x_613);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_620 = x_617;
} else {
 lean_dec_ref(x_617);
 x_620 = lean_box(0);
}
x_621 = lean_ctor_get(x_618, 1);
lean_inc(x_621);
lean_dec(x_618);
x_622 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_602)) {
 x_623 = lean_alloc_ctor(1, 1, 0);
} else {
 x_623 = x_602;
}
lean_ctor_set(x_623, 0, x_601);
x_624 = 0;
x_625 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_625, 0, x_8);
lean_ctor_set(x_625, 1, x_622);
lean_ctor_set(x_625, 2, x_610);
lean_ctor_set(x_625, 3, x_621);
lean_ctor_set(x_625, 4, x_623);
lean_ctor_set(x_625, 5, x_486);
lean_ctor_set_uint8(x_625, sizeof(void*)*6, x_624);
lean_ctor_set_uint8(x_625, sizeof(void*)*6 + 1, x_28);
if (lean_is_scalar(x_620)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_620;
}
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_619);
return x_626;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_606);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_486);
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_627 = lean_ctor_get(x_609, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_609, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_629 = x_609;
} else {
 lean_dec_ref(x_609);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_628);
return x_630;
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
