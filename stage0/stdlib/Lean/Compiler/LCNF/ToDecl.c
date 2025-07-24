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
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___closed__0;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_hasMacroInlineAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__21;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__17;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__5;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__27;
lean_object* l_Lean_getExternAttrData_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
static lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__15;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static uint64_t l_Lean_Compiler_LCNF_inlineMatchers___closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__14;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__5;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__24;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__19;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__7;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__8;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__22;
lean_object* l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
lean_object* l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__2;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__6;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__16;
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__23;
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_dec_ref(x_5);
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
lean_inc(x_6);
x_13 = l_Lean_Compiler_hasMacroInlineAttribute(x_12, x_6);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_14 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; 
lean_free_object(x_8);
x_15 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_6, x_2, x_3, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Core_instantiateValueLevelParams(x_16, x_7, x_2, x_3, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
x_22 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_22);
x_23 = lean_mk_array(x_22, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_22, x_24);
lean_dec(x_22);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_23, x_25);
x_27 = l_Lean_Expr_beta(x_20, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
x_32 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_32);
x_33 = lean_mk_array(x_32, x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_32, x_34);
lean_dec(x_32);
x_36 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_33, x_35);
x_37 = l_Lean_Expr_beta(x_29, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_30);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_8);
x_50 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_50);
lean_dec(x_48);
lean_inc(x_6);
x_51 = l_Lean_Compiler_hasMacroInlineAttribute(x_50, x_6);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_52 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_6, x_2, x_3, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = l_Lean_Core_instantiateValueLevelParams(x_55, x_7, x_2, x_3, x_56);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
x_62 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_62);
x_63 = lean_mk_array(x_62, x_61);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_62, x_64);
lean_dec(x_62);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_63, x_65);
x_67 = l_Lean_Expr_beta(x_58, x_66);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_60)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_60;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_59);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_57, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_7);
lean_dec_ref(x_1);
x_74 = lean_ctor_get(x_54, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_54, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_76 = x_54;
} else {
 lean_dec_ref(x_54);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_78 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_4);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lam__0___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lam__1___boxed), 4, 0);
x_7 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_6, x_5, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_macroInline___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_macroInline___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___lam__0), 7, 1);
lean_closure_set(x_12, 0, x_4);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 1;
x_11 = 0;
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_10, x_11, x_10, x_11, x_12, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = l_Array_append___redArg(x_1, x_5);
x_13 = l_Lean_mkAppN(x_2, x_5);
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_12, x_13, x_3, x_4, x_3, x_4, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_12);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___closed__0;
lean_inc_ref(x_3);
x_10 = lean_array_push(x_9, x_3);
x_11 = l_Lean_Meta_mkLetFVars(x_10, x_3, x_1, x_1, x_2, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_10);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_k", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_eq(x_10, x_1);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_22; lean_object* x_23; uint8_t x_47; 
x_12 = 1;
x_47 = lean_nat_dec_lt(x_1, x_10);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec_ref(x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_48 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_box(x_11);
x_52 = lean_box(x_12);
x_53 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed), 11, 4);
lean_closure_set(x_53, 0, x_3);
lean_closure_set(x_53, 1, x_2);
lean_closure_set(x_53, 2, x_51);
lean_closure_set(x_53, 3, x_52);
x_54 = lean_nat_sub(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_49, x_55, x_53, x_11, x_11, x_5, x_6, x_7, x_8, x_50);
return x_56;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_48;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec_ref(x_2);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_le(x_1, x_57);
if (x_58 == 0)
{
lean_inc(x_10);
lean_inc(x_1);
x_22 = x_1;
x_23 = x_10;
goto block_46;
}
else
{
lean_inc(x_10);
x_22 = x_57;
x_23 = x_10;
goto block_46;
}
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Array_toSubarray___redArg(x_3, x_16, x_17);
x_19 = l_Array_ofSubarray___redArg(x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_mkLambdaFVars(x_19, x_14, x_11, x_12, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_19);
return x_20;
}
block_46:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_inc_ref(x_3);
x_24 = l_Array_toSubarray___redArg(x_3, x_22, x_23);
x_25 = l_Array_ofSubarray___redArg(x_24);
lean_dec_ref(x_24);
x_26 = 1;
x_27 = l_Lean_Meta_mkLambdaFVars(x_25, x_4, x_11, x_12, x_11, x_12, x_26, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1;
x_31 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_30, x_8, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_28);
x_34 = lean_infer_type(x_28, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_box(x_12);
x_38 = lean_box(x_26);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed), 8, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
x_40 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_41 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_32, x_35, x_28, x_39, x_11, x_40, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_le(x_1, x_10);
if (x_45 == 0)
{
lean_dec(x_1);
x_13 = x_26;
x_14 = x_42;
x_15 = x_43;
x_16 = x_44;
x_17 = x_10;
goto block_21;
}
else
{
lean_dec(x_10);
x_13 = x_26;
x_14 = x_42;
x_15 = x_43;
x_16 = x_44;
x_17 = x_1;
goto block_21;
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_41;
}
}
else
{
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_34;
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_27;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_9);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_inc_ref(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2), 9, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = 0;
x_10 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_1, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_6);
x_14 = lean_unbox(x_7);
x_15 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_4);
x_14 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox(x_2);
x_11 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_inc_ref(x_8);
x_16 = lean_array_set(x_2, x_3, x_8);
x_17 = lean_array_push(x_4, x_8);
x_18 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_5, x_6, x_7, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_alt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_14 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Core_instantiateValueLevelParams(x_15, x_2, x_9, x_10, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_Expr_beta(x_18, x_5);
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLetFVars(x_6, x_20, x_21, x_21, x_22, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_23;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_17;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_28);
x_29 = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(x_3);
x_30 = lean_nat_add(x_4, x_29);
lean_dec(x_29);
x_31 = lean_array_fget(x_28, x_4);
lean_dec_ref(x_28);
x_32 = l_Lean_instInhabitedExpr;
x_33 = lean_array_get(x_32, x_5, x_30);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_34 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(x_33, x_31, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
x_38 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_37, x_10, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_35);
x_41 = lean_infer_type(x_35, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed), 13, 7);
lean_closure_set(x_44, 0, x_4);
lean_closure_set(x_44, 1, x_5);
lean_closure_set(x_44, 2, x_30);
lean_closure_set(x_44, 3, x_6);
lean_closure_set(x_44, 4, x_1);
lean_closure_set(x_44, 5, x_2);
lean_closure_set(x_44, 6, x_3);
x_45 = 0;
x_46 = 0;
x_47 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_39, x_42, x_35, x_44, x_45, x_46, x_7, x_8, x_9, x_10, x_43);
return x_47;
}
else
{
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_41;
}
}
else
{
lean_dec(x_30);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_3, x_12, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec_ref(x_7);
lean_inc(x_8);
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_8, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = l_Lean_Expr_getAppNumArgs(x_1);
x_24 = l_Lean_Meta_Match_MatcherInfo_arity(x_22);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_10);
x_26 = lean_nat_dec_lt(x_23, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_free_object(x_11);
x_27 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
lean_inc(x_23);
x_28 = lean_mk_array(x_23, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_23, x_29);
lean_dec(x_23);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_28, x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
x_34 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_22, x_32, x_31, x_33, x_2, x_3, x_4, x_5, x_19);
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
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_46 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_box(x_25);
x_50 = lean_box(x_26);
x_51 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed), 10, 3);
lean_closure_set(x_51, 0, x_1);
lean_closure_set(x_51, 1, x_49);
lean_closure_set(x_51, 2, x_50);
x_52 = lean_nat_sub(x_24, x_23);
lean_dec(x_23);
lean_dec(x_24);
lean_ctor_set(x_11, 0, x_52);
x_53 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_47, x_11, x_51, x_25, x_25, x_2, x_3, x_4, x_5, x_48);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
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
lean_dec(x_24);
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
lean_ctor_set(x_10, 0, x_58);
return x_10;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_11, 0);
lean_inc(x_59);
lean_dec(x_11);
x_60 = l_Lean_Expr_getAppNumArgs(x_1);
x_61 = l_Lean_Meta_Match_MatcherInfo_arity(x_59);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
uint8_t x_63; 
lean_free_object(x_10);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
x_64 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
lean_inc(x_60);
x_65 = lean_mk_array(x_60, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_60, x_66);
lean_dec(x_60);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_65, x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
x_71 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_59, x_69, x_68, x_70, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_81 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_box(x_62);
x_85 = lean_box(x_63);
x_86 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed), 10, 3);
lean_closure_set(x_86, 0, x_1);
lean_closure_set(x_86, 1, x_84);
lean_closure_set(x_86, 2, x_85);
x_87 = lean_nat_sub(x_61, x_60);
lean_dec(x_60);
lean_dec(x_61);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_82, x_88, x_86, x_62, x_62, x_2, x_3, x_4, x_5, x_83);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_92 = x_81;
} else {
 lean_dec_ref(x_81);
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
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_94 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
lean_ctor_set(x_10, 0, x_94);
return x_10;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
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
x_98 = l_Lean_Expr_getAppNumArgs(x_1);
x_99 = l_Lean_Meta_Match_MatcherInfo_arity(x_96);
x_100 = lean_nat_dec_lt(x_99, x_98);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = lean_nat_dec_lt(x_98, x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_99);
lean_dec(x_97);
x_102 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
lean_inc(x_98);
x_103 = lean_mk_array(x_98, x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_98, x_104);
lean_dec(x_98);
x_106 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_103, x_105);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0;
x_109 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher(x_8, x_9, x_96, x_107, x_106, x_108, x_2, x_3, x_4, x_5, x_95);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_110);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; 
lean_dec(x_96);
lean_dec(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_119 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_95);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_box(x_100);
x_123 = lean_box(x_101);
x_124 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed), 10, 3);
lean_closure_set(x_124, 0, x_1);
lean_closure_set(x_124, 1, x_122);
lean_closure_set(x_124, 2, x_123);
x_125 = lean_nat_sub(x_99, x_98);
lean_dec(x_98);
lean_dec(x_99);
if (lean_is_scalar(x_97)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_97;
}
lean_ctor_set(x_126, 0, x_125);
x_127 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_120, x_126, x_124, x_100, x_100, x_2, x_3, x_4, x_5, x_121);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_119, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_130 = x_119;
} else {
 lean_dec_ref(x_119);
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
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_132 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
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
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_134 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_6);
return x_135;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__5;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__4;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__3;
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__2;
x_6 = l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__11;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__10;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__9;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__8;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__15() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__16;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__17;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__15;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__12;
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__19() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 2;
x_2 = 0;
x_3 = 1;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_6, 0, x_5);
lean_ctor_set_uint8(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, 3, x_5);
lean_ctor_set_uint8(x_6, 4, x_5);
lean_ctor_set_uint8(x_6, 5, x_4);
lean_ctor_set_uint8(x_6, 6, x_4);
lean_ctor_set_uint8(x_6, 7, x_5);
lean_ctor_set_uint8(x_6, 8, x_4);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_2);
lean_ctor_set_uint8(x_6, 11, x_4);
lean_ctor_set_uint8(x_6, 12, x_4);
lean_ctor_set_uint8(x_6, 13, x_4);
lean_ctor_set_uint8(x_6, 14, x_1);
lean_ctor_set_uint8(x_6, 15, x_4);
lean_ctor_set_uint8(x_6, 16, x_4);
lean_ctor_set_uint8(x_6, 17, x_4);
lean_ctor_set_uint8(x_6, 18, x_4);
return x_6;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__20() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__19;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__21() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__20;
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__19;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__24() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__23;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__24;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__22;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_6 = lean_box(1);
x_7 = 0;
x_8 = l_Lean_Compiler_LCNF_inlineMatchers___closed__21;
x_9 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_3);
lean_ctor_set(x_9, 5, x_2);
lean_ctor_set(x_9, 6, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*7, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 2, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed), 6, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__2), 6, 0);
x_11 = 0;
x_12 = l_Lean_Compiler_LCNF_inlineMatchers___closed__27;
lean_inc(x_7);
x_13 = l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(x_1, x_10, x_9, x_11, x_11, x_12, x_7, x_2, x_3, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
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
lean_dec(x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_inlineMatchers___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Compiler_LCNF_inlineMatchers___lam__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Compiler_isUnsafeRecName_x3f(x_5);
lean_dec(x_5);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_18 = l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_macroInline___lam__0___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed), 4, 0);
x_6 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0;
x_7 = l_Lean_Core_transform___at___Lean_Core_betaReduce_spec__0(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Lean_Compiler_mkUnsafeRecName(x_1);
x_9 = 0;
lean_inc_ref(x_7);
x_10 = l_Lean_Environment_find_x3f(x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Environment_find_x3f(x_7, x_1, x_9);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_dec_ref(x_7);
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_Compiler_mkUnsafeRecName(x_1);
x_16 = 0;
lean_inc_ref(x_14);
x_17 = l_Lean_Environment_find_x3f(x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Environment_find_x3f(x_14, x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec_ref(x_14);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_getDeclInfo_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 7)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_7);
x_14 = l_Lean_isMarkedBorrowed(x_12);
x_15 = l_Lean_Compiler_LCNF_mkParam(x_11, x_12, x_14, x_2, x_3, x_4, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_array_push(x_9, x_16);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_13);
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_7);
x_24 = l_Lean_isMarkedBorrowed(x_22);
x_25 = l_Lean_Compiler_LCNF_mkParam(x_21, x_22, x_24, x_2, x_3, x_4, x_5, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_array_push(x_20, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_1 = x_29;
x_6 = x_27;
goto _start;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_10 = l_Lean_Meta_etaExpand(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 1;
x_14 = l_Lean_Meta_mkLambdaFVars(x_3, x_11, x_1, x_2, x_1, x_2, x_13, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_14;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__0() {
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
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declaration `", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` does not have a value", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` not found", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_toDecl___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_379; lean_object* x_404; 
x_404 = l_Lean_Compiler_isUnsafeRecName_x3f(x_1);
if (lean_obj_tag(x_404) == 0)
{
x_379 = x_1;
goto block_403;
}
else
{
lean_object* x_405; 
lean_dec(x_1);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec_ref(x_404);
x_379 = x_405;
goto block_403;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_ConstantInfo_levelParams(x_14);
lean_dec_ref(x_14);
x_21 = lean_mk_empty_array_with_capacity(x_13);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
x_23 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_7);
lean_ctor_set_uint8(x_23, sizeof(void*)*6, x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*6 + 1, x_12);
x_24 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_23, x_15, x_16, x_17, x_18, x_19);
return x_24;
}
block_46:
{
lean_object* x_34; uint8_t x_35; 
lean_inc_ref(x_32);
x_34 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_32, x_2, x_3, x_4, x_5, x_33);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_ConstantInfo_levelParams(x_31);
lean_dec_ref(x_31);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_39 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_27);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 1, x_29);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = l_Lean_ConstantInfo_levelParams(x_31);
lean_dec_ref(x_31);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_30);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_28);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_32);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_26);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_27);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_29);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
block_66:
{
lean_object* x_54; uint8_t x_55; 
lean_inc_ref(x_52);
x_54 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_52, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Lean_ConstantInfo_levelParams(x_51);
lean_dec_ref(x_51);
x_58 = l_Lean_Compiler_LCNF_toDecl___closed__1;
x_59 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_47);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_50);
lean_ctor_set_uint8(x_59, sizeof(void*)*6 + 1, x_49);
lean_ctor_set(x_54, 0, x_59);
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
x_62 = l_Lean_ConstantInfo_levelParams(x_51);
lean_dec_ref(x_51);
x_63 = l_Lean_Compiler_LCNF_toDecl___closed__1;
x_64 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_64, 0, x_48);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_52);
lean_ctor_set(x_64, 3, x_60);
lean_ctor_set(x_64, 4, x_63);
lean_ctor_set(x_64, 5, x_47);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_50);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 1, x_49);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
block_378:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_st_ref_get(x_5, x_68);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_75);
lean_dec(x_73);
lean_inc(x_67);
lean_inc_ref(x_75);
x_76 = l_Lean_Compiler_getInlineAttribute_x3f(x_75, x_67);
lean_inc(x_67);
lean_inc_ref(x_75);
x_77 = l_Lean_getExternAttrData_x3f(x_75, x_67);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
lean_inc(x_67);
x_78 = l_Lean_hasInitAttr(x_75, x_67);
if (x_78 == 0)
{
uint8_t x_79; lean_object* x_80; 
x_79 = 1;
lean_inc_ref(x_69);
x_80 = l_Lean_ConstantInfo_value_x3f(x_69, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec_ref(x_2);
x_81 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_82 = l_Lean_MessageData_ofName(x_67);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_82);
lean_ctor_set(x_71, 0, x_81);
x_83 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_84, x_3, x_4, x_5, x_74);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_71);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
lean_dec_ref(x_80);
x_87 = lean_box(1);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_90 = lean_st_mk_ref(x_89, x_74);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = l_Lean_ConstantInfo_type(x_69);
x_94 = 1;
x_95 = 0;
x_96 = 2;
x_97 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_97, 0, x_78);
lean_ctor_set_uint8(x_97, 1, x_78);
lean_ctor_set_uint8(x_97, 2, x_78);
lean_ctor_set_uint8(x_97, 3, x_78);
lean_ctor_set_uint8(x_97, 4, x_78);
lean_ctor_set_uint8(x_97, 5, x_79);
lean_ctor_set_uint8(x_97, 6, x_79);
lean_ctor_set_uint8(x_97, 7, x_78);
lean_ctor_set_uint8(x_97, 8, x_79);
lean_ctor_set_uint8(x_97, 9, x_94);
lean_ctor_set_uint8(x_97, 10, x_95);
lean_ctor_set_uint8(x_97, 11, x_79);
lean_ctor_set_uint8(x_97, 12, x_79);
lean_ctor_set_uint8(x_97, 13, x_79);
lean_ctor_set_uint8(x_97, 14, x_96);
lean_ctor_set_uint8(x_97, 15, x_79);
lean_ctor_set_uint8(x_97, 16, x_79);
lean_ctor_set_uint8(x_97, 17, x_79);
lean_ctor_set_uint8(x_97, 18, x_79);
x_98 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_97);
x_99 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint64(x_99, sizeof(void*)*1, x_98);
x_100 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_101 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
x_102 = lean_box(0);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_87);
lean_ctor_set(x_104, 2, x_100);
lean_ctor_set(x_104, 3, x_101);
lean_ctor_set(x_104, 4, x_102);
lean_ctor_set(x_104, 5, x_88);
lean_ctor_set(x_104, 6, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*7, x_78);
lean_ctor_set_uint8(x_104, sizeof(void*)*7 + 1, x_78);
lean_ctor_set_uint8(x_104, sizeof(void*)*7 + 2, x_78);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_91);
lean_inc_ref(x_104);
x_105 = l_Lean_Compiler_LCNF_toLCNFType(x_93, x_104, x_91, x_4, x_5, x_92);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec_ref(x_105);
x_108 = lean_box(x_78);
x_109 = lean_box(x_79);
x_110 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(x_110, 0, x_108);
lean_closure_set(x_110, 1, x_109);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_91);
x_111 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_86, x_110, x_78, x_104, x_91, x_4, x_5, x_107);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
lean_inc(x_5);
lean_inc_ref(x_4);
x_114 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(x_112, x_4, x_5, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
lean_inc(x_5);
lean_inc_ref(x_4);
x_117 = l_Lean_Compiler_LCNF_macroInline(x_115, x_4, x_5, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
lean_inc(x_5);
lean_inc_ref(x_4);
x_120 = l_Lean_Compiler_LCNF_inlineMatchers(x_118, x_4, x_5, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
lean_inc(x_5);
lean_inc_ref(x_4);
x_123 = l_Lean_Compiler_LCNF_macroInline(x_121, x_4, x_5, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_st_ref_get(x_91, x_125);
lean_dec(x_91);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_128 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_124, x_2, x_3, x_4, x_5, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 1)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc_ref(x_130);
if (lean_obj_tag(x_130) == 5)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec_ref(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_132);
lean_dec_ref(x_129);
x_133 = !lean_is_exclusive(x_130);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_130, 0);
lean_dec(x_134);
x_135 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_132, x_78, x_3, x_131);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_ctor_get(x_132, 2);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_132, 4);
lean_inc_ref(x_138);
lean_dec_ref(x_132);
x_139 = l_Lean_ConstantInfo_levelParams(x_69);
lean_dec_ref(x_69);
lean_ctor_set_tag(x_130, 0);
lean_ctor_set(x_130, 0, x_138);
x_140 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_140, 0, x_67);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_106);
lean_ctor_set(x_140, 3, x_137);
lean_ctor_set(x_140, 4, x_130);
lean_ctor_set(x_140, 5, x_76);
lean_ctor_set_uint8(x_140, sizeof(void*)*6, x_78);
lean_ctor_set_uint8(x_140, sizeof(void*)*6 + 1, x_70);
x_141 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_140, x_2, x_3, x_4, x_5, x_136);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_130);
x_142 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_132, x_78, x_3, x_131);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_ctor_get(x_132, 2);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_132, 4);
lean_inc_ref(x_145);
lean_dec_ref(x_132);
x_146 = l_Lean_ConstantInfo_levelParams(x_69);
lean_dec_ref(x_69);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_145);
x_148 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_148, 0, x_67);
lean_ctor_set(x_148, 1, x_146);
lean_ctor_set(x_148, 2, x_106);
lean_ctor_set(x_148, 3, x_144);
lean_ctor_set(x_148, 4, x_147);
lean_ctor_set(x_148, 5, x_76);
lean_ctor_set_uint8(x_148, sizeof(void*)*6, x_78);
lean_ctor_set_uint8(x_148, sizeof(void*)*6 + 1, x_70);
x_149 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_148, x_2, x_3, x_4, x_5, x_143);
return x_149;
}
}
else
{
lean_object* x_150; 
lean_dec_ref(x_130);
x_150 = lean_ctor_get(x_128, 1);
lean_inc(x_150);
lean_dec_ref(x_128);
x_7 = x_76;
x_8 = x_67;
x_9 = x_129;
x_10 = x_78;
x_11 = x_106;
x_12 = x_70;
x_13 = x_88;
x_14 = x_69;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_150;
goto block_25;
}
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
lean_dec_ref(x_128);
x_7 = x_76;
x_8 = x_67;
x_9 = x_129;
x_10 = x_78;
x_11 = x_106;
x_12 = x_70;
x_13 = x_88;
x_14 = x_69;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_151;
goto block_25;
}
}
else
{
uint8_t x_152; 
lean_dec(x_106);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_152 = !lean_is_exclusive(x_128);
if (x_152 == 0)
{
return x_128;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_128, 0);
x_154 = lean_ctor_get(x_128, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_128);
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
lean_dec(x_106);
lean_dec(x_91);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_156 = !lean_is_exclusive(x_123);
if (x_156 == 0)
{
return x_123;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_123, 0);
x_158 = lean_ctor_get(x_123, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_123);
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
lean_dec(x_106);
lean_dec(x_91);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_160 = !lean_is_exclusive(x_120);
if (x_160 == 0)
{
return x_120;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_120, 0);
x_162 = lean_ctor_get(x_120, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_120);
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
lean_dec(x_106);
lean_dec(x_91);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_164 = !lean_is_exclusive(x_117);
if (x_164 == 0)
{
return x_117;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_117, 0);
x_166 = lean_ctor_get(x_117, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_117);
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
lean_dec(x_106);
lean_dec(x_91);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_168 = !lean_is_exclusive(x_114);
if (x_168 == 0)
{
return x_114;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_114, 0);
x_170 = lean_ctor_get(x_114, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_114);
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
lean_dec(x_106);
lean_dec(x_91);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_172 = !lean_is_exclusive(x_111);
if (x_172 == 0)
{
return x_111;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_111, 0);
x_174 = lean_ctor_get(x_111, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_111);
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
lean_dec_ref(x_104);
lean_dec(x_91);
lean_dec(x_86);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_176 = !lean_is_exclusive(x_105);
if (x_176 == 0)
{
return x_105;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_105, 0);
x_178 = lean_ctor_get(x_105, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_105);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; uint64_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_free_object(x_71);
x_180 = lean_box(1);
x_181 = lean_unsigned_to_nat(0u);
x_182 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_183 = lean_st_mk_ref(x_182, x_74);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec_ref(x_183);
x_186 = l_Lean_ConstantInfo_type(x_69);
x_187 = 0;
x_188 = 1;
x_189 = 0;
x_190 = 2;
x_191 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_191, 0, x_187);
lean_ctor_set_uint8(x_191, 1, x_187);
lean_ctor_set_uint8(x_191, 2, x_187);
lean_ctor_set_uint8(x_191, 3, x_187);
lean_ctor_set_uint8(x_191, 4, x_187);
lean_ctor_set_uint8(x_191, 5, x_78);
lean_ctor_set_uint8(x_191, 6, x_78);
lean_ctor_set_uint8(x_191, 7, x_187);
lean_ctor_set_uint8(x_191, 8, x_78);
lean_ctor_set_uint8(x_191, 9, x_188);
lean_ctor_set_uint8(x_191, 10, x_189);
lean_ctor_set_uint8(x_191, 11, x_78);
lean_ctor_set_uint8(x_191, 12, x_78);
lean_ctor_set_uint8(x_191, 13, x_78);
lean_ctor_set_uint8(x_191, 14, x_190);
lean_ctor_set_uint8(x_191, 15, x_78);
lean_ctor_set_uint8(x_191, 16, x_78);
lean_ctor_set_uint8(x_191, 17, x_78);
lean_ctor_set_uint8(x_191, 18, x_78);
x_192 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_191);
x_193 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set_uint64(x_193, sizeof(void*)*1, x_192);
x_194 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_195 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
x_196 = lean_box(0);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_180);
lean_ctor_set(x_198, 2, x_194);
lean_ctor_set(x_198, 3, x_195);
lean_ctor_set(x_198, 4, x_196);
lean_ctor_set(x_198, 5, x_181);
lean_ctor_set(x_198, 6, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*7, x_187);
lean_ctor_set_uint8(x_198, sizeof(void*)*7 + 1, x_187);
lean_ctor_set_uint8(x_198, sizeof(void*)*7 + 2, x_187);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_184);
x_199 = l_Lean_Compiler_LCNF_toLCNFType(x_186, x_198, x_184, x_4, x_5, x_185);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec_ref(x_199);
x_202 = lean_st_ref_get(x_184, x_201);
lean_dec(x_184);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec_ref(x_202);
x_47 = x_76;
x_48 = x_67;
x_49 = x_70;
x_50 = x_187;
x_51 = x_69;
x_52 = x_200;
x_53 = x_203;
goto block_66;
}
else
{
lean_dec(x_184);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 1);
lean_inc(x_205);
lean_dec_ref(x_199);
x_47 = x_76;
x_48 = x_67;
x_49 = x_70;
x_50 = x_187;
x_51 = x_69;
x_52 = x_204;
x_53 = x_205;
goto block_66;
}
else
{
uint8_t x_206; 
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_206 = !lean_is_exclusive(x_199);
if (x_206 == 0)
{
return x_199;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_199, 0);
x_208 = lean_ctor_get(x_199, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_199);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; 
lean_dec_ref(x_75);
lean_free_object(x_71);
x_210 = lean_ctor_get(x_77, 0);
lean_inc(x_210);
lean_dec_ref(x_77);
x_211 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_212 = lean_st_mk_ref(x_211, x_74);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec_ref(x_212);
x_215 = l_Lean_ConstantInfo_type(x_69);
x_216 = 0;
x_217 = l_Lean_Compiler_LCNF_inlineMatchers___closed__27;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_213);
x_218 = l_Lean_Compiler_LCNF_toLCNFType(x_215, x_217, x_213, x_4, x_5, x_214);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = lean_st_ref_get(x_213, x_220);
lean_dec(x_213);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec_ref(x_221);
x_26 = x_76;
x_27 = x_216;
x_28 = x_67;
x_29 = x_70;
x_30 = x_210;
x_31 = x_69;
x_32 = x_219;
x_33 = x_222;
goto block_46;
}
else
{
lean_dec(x_213);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_218, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_218, 1);
lean_inc(x_224);
lean_dec_ref(x_218);
x_26 = x_76;
x_27 = x_216;
x_28 = x_67;
x_29 = x_70;
x_30 = x_210;
x_31 = x_69;
x_32 = x_223;
x_33 = x_224;
goto block_46;
}
else
{
uint8_t x_225; 
lean_dec(x_210);
lean_dec(x_76);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_225 = !lean_is_exclusive(x_218);
if (x_225 == 0)
{
return x_218;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_218, 0);
x_227 = lean_ctor_get(x_218, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_218);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_71, 0);
x_230 = lean_ctor_get(x_71, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_71);
x_231 = lean_ctor_get(x_229, 0);
lean_inc_ref(x_231);
lean_dec(x_229);
lean_inc(x_67);
lean_inc_ref(x_231);
x_232 = l_Lean_Compiler_getInlineAttribute_x3f(x_231, x_67);
lean_inc(x_67);
lean_inc_ref(x_231);
x_233 = l_Lean_getExternAttrData_x3f(x_231, x_67);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
lean_inc(x_67);
x_234 = l_Lean_hasInitAttr(x_231, x_67);
if (x_234 == 0)
{
uint8_t x_235; lean_object* x_236; 
x_235 = 1;
lean_inc_ref(x_69);
x_236 = l_Lean_ConstantInfo_value_x3f(x_69, x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec_ref(x_2);
x_237 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_238 = l_Lean_MessageData_ofName(x_67);
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_241, x_3, x_4, x_5, x_230);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; lean_object* x_254; uint64_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_243 = lean_ctor_get(x_236, 0);
lean_inc(x_243);
lean_dec_ref(x_236);
x_244 = lean_box(1);
x_245 = lean_unsigned_to_nat(0u);
x_246 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_247 = lean_st_mk_ref(x_246, x_230);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec_ref(x_247);
x_250 = l_Lean_ConstantInfo_type(x_69);
x_251 = 1;
x_252 = 0;
x_253 = 2;
x_254 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_254, 0, x_234);
lean_ctor_set_uint8(x_254, 1, x_234);
lean_ctor_set_uint8(x_254, 2, x_234);
lean_ctor_set_uint8(x_254, 3, x_234);
lean_ctor_set_uint8(x_254, 4, x_234);
lean_ctor_set_uint8(x_254, 5, x_235);
lean_ctor_set_uint8(x_254, 6, x_235);
lean_ctor_set_uint8(x_254, 7, x_234);
lean_ctor_set_uint8(x_254, 8, x_235);
lean_ctor_set_uint8(x_254, 9, x_251);
lean_ctor_set_uint8(x_254, 10, x_252);
lean_ctor_set_uint8(x_254, 11, x_235);
lean_ctor_set_uint8(x_254, 12, x_235);
lean_ctor_set_uint8(x_254, 13, x_235);
lean_ctor_set_uint8(x_254, 14, x_253);
lean_ctor_set_uint8(x_254, 15, x_235);
lean_ctor_set_uint8(x_254, 16, x_235);
lean_ctor_set_uint8(x_254, 17, x_235);
lean_ctor_set_uint8(x_254, 18, x_235);
x_255 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_254);
x_256 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set_uint64(x_256, sizeof(void*)*1, x_255);
x_257 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_258 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
x_259 = lean_box(0);
x_260 = lean_box(0);
x_261 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_244);
lean_ctor_set(x_261, 2, x_257);
lean_ctor_set(x_261, 3, x_258);
lean_ctor_set(x_261, 4, x_259);
lean_ctor_set(x_261, 5, x_245);
lean_ctor_set(x_261, 6, x_260);
lean_ctor_set_uint8(x_261, sizeof(void*)*7, x_234);
lean_ctor_set_uint8(x_261, sizeof(void*)*7 + 1, x_234);
lean_ctor_set_uint8(x_261, sizeof(void*)*7 + 2, x_234);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_248);
lean_inc_ref(x_261);
x_262 = l_Lean_Compiler_LCNF_toLCNFType(x_250, x_261, x_248, x_4, x_5, x_249);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec_ref(x_262);
x_265 = lean_box(x_234);
x_266 = lean_box(x_235);
x_267 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(x_267, 0, x_265);
lean_closure_set(x_267, 1, x_266);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_248);
x_268 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_243, x_267, x_234, x_261, x_248, x_4, x_5, x_264);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec_ref(x_268);
lean_inc(x_5);
lean_inc_ref(x_4);
x_271 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(x_269, x_4, x_5, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec_ref(x_271);
lean_inc(x_5);
lean_inc_ref(x_4);
x_274 = l_Lean_Compiler_LCNF_macroInline(x_272, x_4, x_5, x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec_ref(x_274);
lean_inc(x_5);
lean_inc_ref(x_4);
x_277 = l_Lean_Compiler_LCNF_inlineMatchers(x_275, x_4, x_5, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec_ref(x_277);
lean_inc(x_5);
lean_inc_ref(x_4);
x_280 = l_Lean_Compiler_LCNF_macroInline(x_278, x_4, x_5, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec_ref(x_280);
x_283 = lean_st_ref_get(x_248, x_282);
lean_dec(x_248);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec_ref(x_283);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_285 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_281, x_2, x_3, x_4, x_5, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
if (lean_obj_tag(x_286) == 1)
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_286, 1);
lean_inc_ref(x_287);
if (lean_obj_tag(x_287) == 5)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
lean_dec_ref(x_285);
x_289 = lean_ctor_get(x_286, 0);
lean_inc_ref(x_289);
lean_dec_ref(x_286);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
x_291 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_289, x_234, x_3, x_288);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = lean_ctor_get(x_289, 2);
lean_inc_ref(x_293);
x_294 = lean_ctor_get(x_289, 4);
lean_inc_ref(x_294);
lean_dec_ref(x_289);
x_295 = l_Lean_ConstantInfo_levelParams(x_69);
lean_dec_ref(x_69);
if (lean_is_scalar(x_290)) {
 x_296 = lean_alloc_ctor(0, 1, 0);
} else {
 x_296 = x_290;
 lean_ctor_set_tag(x_296, 0);
}
lean_ctor_set(x_296, 0, x_294);
x_297 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_297, 0, x_67);
lean_ctor_set(x_297, 1, x_295);
lean_ctor_set(x_297, 2, x_263);
lean_ctor_set(x_297, 3, x_293);
lean_ctor_set(x_297, 4, x_296);
lean_ctor_set(x_297, 5, x_232);
lean_ctor_set_uint8(x_297, sizeof(void*)*6, x_234);
lean_ctor_set_uint8(x_297, sizeof(void*)*6 + 1, x_70);
x_298 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_297, x_2, x_3, x_4, x_5, x_292);
return x_298;
}
else
{
lean_object* x_299; 
lean_dec_ref(x_287);
x_299 = lean_ctor_get(x_285, 1);
lean_inc(x_299);
lean_dec_ref(x_285);
x_7 = x_232;
x_8 = x_67;
x_9 = x_286;
x_10 = x_234;
x_11 = x_263;
x_12 = x_70;
x_13 = x_245;
x_14 = x_69;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_299;
goto block_25;
}
}
else
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_285, 1);
lean_inc(x_300);
lean_dec_ref(x_285);
x_7 = x_232;
x_8 = x_67;
x_9 = x_286;
x_10 = x_234;
x_11 = x_263;
x_12 = x_70;
x_13 = x_245;
x_14 = x_69;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_300;
goto block_25;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_263);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_301 = lean_ctor_get(x_285, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_285, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_303 = x_285;
} else {
 lean_dec_ref(x_285);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_263);
lean_dec(x_248);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_305 = lean_ctor_get(x_280, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_280, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_307 = x_280;
} else {
 lean_dec_ref(x_280);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_306);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_263);
lean_dec(x_248);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_309 = lean_ctor_get(x_277, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_277, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_311 = x_277;
} else {
 lean_dec_ref(x_277);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_263);
lean_dec(x_248);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_313 = lean_ctor_get(x_274, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_274, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_315 = x_274;
} else {
 lean_dec_ref(x_274);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_263);
lean_dec(x_248);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_317 = lean_ctor_get(x_271, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_271, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_319 = x_271;
} else {
 lean_dec_ref(x_271);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_263);
lean_dec(x_248);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_321 = lean_ctor_get(x_268, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_268, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_323 = x_268;
} else {
 lean_dec_ref(x_268);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec_ref(x_261);
lean_dec(x_248);
lean_dec(x_243);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_325 = lean_ctor_get(x_262, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_262, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_327 = x_262;
} else {
 lean_dec_ref(x_262);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; uint8_t x_337; uint8_t x_338; uint8_t x_339; lean_object* x_340; uint64_t x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_329 = lean_box(1);
x_330 = lean_unsigned_to_nat(0u);
x_331 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_332 = lean_st_mk_ref(x_331, x_230);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec_ref(x_332);
x_335 = l_Lean_ConstantInfo_type(x_69);
x_336 = 0;
x_337 = 1;
x_338 = 0;
x_339 = 2;
x_340 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_340, 0, x_336);
lean_ctor_set_uint8(x_340, 1, x_336);
lean_ctor_set_uint8(x_340, 2, x_336);
lean_ctor_set_uint8(x_340, 3, x_336);
lean_ctor_set_uint8(x_340, 4, x_336);
lean_ctor_set_uint8(x_340, 5, x_234);
lean_ctor_set_uint8(x_340, 6, x_234);
lean_ctor_set_uint8(x_340, 7, x_336);
lean_ctor_set_uint8(x_340, 8, x_234);
lean_ctor_set_uint8(x_340, 9, x_337);
lean_ctor_set_uint8(x_340, 10, x_338);
lean_ctor_set_uint8(x_340, 11, x_234);
lean_ctor_set_uint8(x_340, 12, x_234);
lean_ctor_set_uint8(x_340, 13, x_234);
lean_ctor_set_uint8(x_340, 14, x_339);
lean_ctor_set_uint8(x_340, 15, x_234);
lean_ctor_set_uint8(x_340, 16, x_234);
lean_ctor_set_uint8(x_340, 17, x_234);
lean_ctor_set_uint8(x_340, 18, x_234);
x_341 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_340);
x_342 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set_uint64(x_342, sizeof(void*)*1, x_341);
x_343 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_344 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
x_345 = lean_box(0);
x_346 = lean_box(0);
x_347 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_329);
lean_ctor_set(x_347, 2, x_343);
lean_ctor_set(x_347, 3, x_344);
lean_ctor_set(x_347, 4, x_345);
lean_ctor_set(x_347, 5, x_330);
lean_ctor_set(x_347, 6, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*7, x_336);
lean_ctor_set_uint8(x_347, sizeof(void*)*7 + 1, x_336);
lean_ctor_set_uint8(x_347, sizeof(void*)*7 + 2, x_336);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_333);
x_348 = l_Lean_Compiler_LCNF_toLCNFType(x_335, x_347, x_333, x_4, x_5, x_334);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec_ref(x_348);
x_351 = lean_st_ref_get(x_333, x_350);
lean_dec(x_333);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec_ref(x_351);
x_47 = x_232;
x_48 = x_67;
x_49 = x_70;
x_50 = x_336;
x_51 = x_69;
x_52 = x_349;
x_53 = x_352;
goto block_66;
}
else
{
lean_dec(x_333);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_348, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_348, 1);
lean_inc(x_354);
lean_dec_ref(x_348);
x_47 = x_232;
x_48 = x_67;
x_49 = x_70;
x_50 = x_336;
x_51 = x_69;
x_52 = x_353;
x_53 = x_354;
goto block_66;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_355 = lean_ctor_get(x_348, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_348, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_357 = x_348;
} else {
 lean_dec_ref(x_348);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; lean_object* x_367; 
lean_dec_ref(x_231);
x_359 = lean_ctor_get(x_233, 0);
lean_inc(x_359);
lean_dec_ref(x_233);
x_360 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_361 = lean_st_mk_ref(x_360, x_230);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec_ref(x_361);
x_364 = l_Lean_ConstantInfo_type(x_69);
x_365 = 0;
x_366 = l_Lean_Compiler_LCNF_inlineMatchers___closed__27;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_362);
x_367 = l_Lean_Compiler_LCNF_toLCNFType(x_364, x_366, x_362, x_4, x_5, x_363);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec_ref(x_367);
x_370 = lean_st_ref_get(x_362, x_369);
lean_dec(x_362);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec_ref(x_370);
x_26 = x_232;
x_27 = x_365;
x_28 = x_67;
x_29 = x_70;
x_30 = x_359;
x_31 = x_69;
x_32 = x_368;
x_33 = x_371;
goto block_46;
}
else
{
lean_dec(x_362);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_367, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_367, 1);
lean_inc(x_373);
lean_dec_ref(x_367);
x_26 = x_232;
x_27 = x_365;
x_28 = x_67;
x_29 = x_70;
x_30 = x_359;
x_31 = x_69;
x_32 = x_372;
x_33 = x_373;
goto block_46;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_359);
lean_dec(x_232);
lean_dec_ref(x_69);
lean_dec(x_67);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_374 = lean_ctor_get(x_367, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_367, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_376 = x_367;
} else {
 lean_dec_ref(x_367);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_374);
lean_ctor_set(x_377, 1, x_375);
return x_377;
}
}
}
}
}
block_403:
{
lean_object* x_380; lean_object* x_381; 
lean_inc(x_379);
x_380 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_379, x_5, x_6);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
uint8_t x_382; 
lean_dec_ref(x_2);
x_382 = !lean_is_exclusive(x_380);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_383 = lean_ctor_get(x_380, 1);
x_384 = lean_ctor_get(x_380, 0);
lean_dec(x_384);
x_385 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_386 = l_Lean_MessageData_ofName(x_379);
lean_ctor_set_tag(x_380, 7);
lean_ctor_set(x_380, 1, x_386);
lean_ctor_set(x_380, 0, x_385);
x_387 = l_Lean_Compiler_LCNF_toDecl___closed__7;
x_388 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_388, 0, x_380);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_388, x_3, x_4, x_5, x_383);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_389;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_380, 1);
lean_inc(x_390);
lean_dec(x_380);
x_391 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_392 = l_Lean_MessageData_ofName(x_379);
x_393 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = l_Lean_Compiler_LCNF_toDecl___closed__7;
x_395 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_395, x_3, x_4, x_5, x_390);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_396;
}
}
else
{
lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_397 = lean_ctor_get(x_380, 1);
lean_inc(x_397);
lean_dec_ref(x_380);
x_398 = lean_ctor_get(x_381, 0);
lean_inc(x_398);
lean_dec_ref(x_381);
x_399 = l_Lean_ConstantInfo_isPartial(x_398);
if (x_399 == 0)
{
uint8_t x_400; 
x_400 = l_Lean_ConstantInfo_isUnsafe(x_398);
if (x_400 == 0)
{
uint8_t x_401; 
x_401 = 1;
x_67 = x_379;
x_68 = x_397;
x_69 = x_398;
x_70 = x_401;
goto block_378;
}
else
{
x_67 = x_379;
x_68 = x_397;
x_69 = x_398;
x_70 = x_399;
goto block_378;
}
}
else
{
uint8_t x_402; 
x_402 = 0;
x_67 = x_379;
x_68 = x_397;
x_69 = x_398;
x_70 = x_402;
goto block_378;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_2);
x_12 = l_Lean_Compiler_LCNF_toDecl___lam__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_12;
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
l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0 = _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_macroInline___lam__1___closed__0);
l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1 = _init_l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___closed__0 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___closed__0);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__0);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__0);
l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1 = _init_l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1);
l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0 = _init_l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___lam__2___closed__0);
l_Lean_Compiler_LCNF_inlineMatchers___closed__0 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__0);
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
l_Lean_Compiler_LCNF_inlineMatchers___closed__21 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__21);
l_Lean_Compiler_LCNF_inlineMatchers___closed__22 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__22);
l_Lean_Compiler_LCNF_inlineMatchers___closed__23 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__23);
l_Lean_Compiler_LCNF_inlineMatchers___closed__24 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__24);
l_Lean_Compiler_LCNF_inlineMatchers___closed__25 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__25();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__25);
l_Lean_Compiler_LCNF_inlineMatchers___closed__26 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__26();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__26);
l_Lean_Compiler_LCNF_inlineMatchers___closed__27 = _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__27();
lean_mark_persistent(l_Lean_Compiler_LCNF_inlineMatchers___closed__27);
l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0 = _init_l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames___closed__0);
l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0);
l_Lean_Compiler_LCNF_toDecl___closed__0 = _init_l_Lean_Compiler_LCNF_toDecl___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_toDecl___closed__0);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
