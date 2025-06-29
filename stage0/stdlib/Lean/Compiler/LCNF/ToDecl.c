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
lean_object* lean_get_extern_attr_data(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__6;
static lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__15;
static lean_object* l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t lean_is_marked_borrowed(lean_object*);
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
lean_object* lean_is_unsafe_rec_name(lean_object*);
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
lean_object* lean_mk_unsafe_rec_name(lean_object*);
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
lean_dec(x_5);
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
x_13 = l_Lean_Compiler_hasMacroInlineAttribute(x_12, x_6);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_dec(x_15);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_6);
x_51 = l_Lean_Compiler_hasMacroInlineAttribute(x_50, x_6);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_dec(x_54);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_macroInline___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_macroInline___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___lam__0), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(1);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_unbox(x_10);
x_14 = lean_unbox(x_11);
x_15 = lean_unbox(x_10);
x_16 = lean_unbox(x_11);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_13, x_14, x_15, x_16, x_12, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = l_Array_append___redArg(x_1, x_5);
x_13 = l_Lean_mkAppN(x_2, x_5);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Meta_mkLambdaFVars(x_12, x_13, x_3, x_4, x_3, x_4, x_15, x_7, x_8, x_9, x_10, x_11);
return x_16;
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
lean_inc(x_3);
x_10 = lean_array_push(x_9, x_3);
x_11 = l_Lean_Meta_mkLetFVars(x_10, x_3, x_1, x_1, x_2, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_24; lean_object* x_25; uint8_t x_53; 
x_12 = lean_box(1);
x_53 = lean_nat_dec_lt(x_1, x_10);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_54 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(x_11);
x_58 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed), 11, 4);
lean_closure_set(x_58, 0, x_3);
lean_closure_set(x_58, 1, x_2);
lean_closure_set(x_58, 2, x_57);
lean_closure_set(x_58, 3, x_12);
x_59 = lean_nat_sub(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_55, x_60, x_58, x_11, x_11, x_5, x_6, x_7, x_8, x_56);
return x_61;
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_54;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_2);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_le(x_1, x_62);
if (x_63 == 0)
{
lean_inc(x_10);
lean_inc(x_1);
x_24 = x_1;
x_25 = x_10;
goto block_52;
}
else
{
lean_inc(x_10);
x_24 = x_62;
x_25 = x_10;
goto block_52;
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_18 = l_Array_toSubarray___redArg(x_3, x_16, x_17);
x_19 = l_Array_ofSubarray___redArg(x_18);
lean_dec(x_18);
x_20 = lean_unbox(x_12);
x_21 = lean_unbox(x_12);
x_22 = l_Lean_Meta_mkLambdaFVars(x_19, x_15, x_11, x_20, x_11, x_21, x_13, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
block_52:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
lean_inc(x_3);
x_26 = l_Array_toSubarray___redArg(x_3, x_24, x_25);
x_27 = l_Array_ofSubarray___redArg(x_26);
lean_dec(x_26);
x_28 = lean_box(1);
x_29 = lean_unbox(x_12);
x_30 = lean_unbox(x_12);
x_31 = lean_unbox(x_28);
x_32 = l_Lean_Meta_mkLambdaFVars(x_27, x_4, x_11, x_29, x_11, x_30, x_31, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2___closed__1;
x_36 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_35, x_8, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_33);
x_39 = lean_infer_type(x_33, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed), 8, 2);
lean_closure_set(x_42, 0, x_12);
lean_closure_set(x_42, 1, x_28);
x_43 = lean_box(0);
x_44 = lean_unbox(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_37, x_40, x_33, x_42, x_11, x_44, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_le(x_1, x_10);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_1);
x_50 = lean_unbox(x_28);
x_13 = x_50;
x_14 = x_47;
x_15 = x_46;
x_16 = x_48;
x_17 = x_10;
goto block_23;
}
else
{
uint8_t x_51; 
lean_dec(x_10);
x_51 = lean_unbox(x_28);
x_13 = x_51;
x_14 = x_47;
x_15 = x_46;
x_16 = x_48;
x_17 = x_1;
goto block_23;
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_45;
}
}
else
{
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_39;
}
}
else
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_32;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_9);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__2), 9, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_1, x_8, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0(x_1, x_2, x_3, x_4, x_5, x_13, x_14, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt___lam__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_3);
x_14 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Core_instantiateValueLevelParams(x_15, x_2, x_9, x_10, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_beta(x_18, x_5);
x_21 = lean_box(1);
x_22 = lean_box(1);
x_23 = lean_unbox(x_21);
x_24 = lean_unbox(x_21);
x_25 = lean_unbox(x_22);
x_26 = l_Lean_Meta_mkLetFVars(x_6, x_20, x_23, x_24, x_25, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_26;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
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
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
x_32 = l_Lean_Meta_Match_MatcherInfo_getFirstAltPos(x_3);
x_33 = lean_nat_add(x_4, x_32);
lean_dec(x_32);
x_34 = lean_array_fget(x_31, x_4);
lean_dec(x_31);
x_35 = l_Lean_instInhabitedExpr;
x_36 = lean_array_get(x_35, x_5, x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt(x_36, x_34, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___closed__1;
x_41 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_40, x_10, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_38);
x_44 = lean_infer_type(x_38, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers_inlineMatcher___lam__0___boxed), 13, 7);
lean_closure_set(x_47, 0, x_4);
lean_closure_set(x_47, 1, x_5);
lean_closure_set(x_47, 2, x_33);
lean_closure_set(x_47, 3, x_6);
lean_closure_set(x_47, 4, x_1);
lean_closure_set(x_47, 5, x_2);
lean_closure_set(x_47, 6, x_3);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_unbox(x_48);
x_51 = lean_unbox(x_49);
x_52 = l_Lean_Meta_withLetDecl___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__0___redArg(x_42, x_45, x_38, x_47, x_50, x_51, x_7, x_8, x_9, x_10, x_46);
return x_52;
}
else
{
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_33);
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
return x_44;
}
}
else
{
lean_dec(x_33);
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
return x_37;
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_3, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_dec(x_7);
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
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_46 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_81 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_119 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_95);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_3 = lean_box(0);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 0, 19);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 3, x_10);
x_11 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 4, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 5, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 6, x_13);
x_14 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 7, x_14);
x_15 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, 9, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 10, x_17);
x_18 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 11, x_18);
x_19 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 12, x_19);
x_20 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 13, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 14, x_21);
x_22 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 15, x_22);
x_23 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 17, x_24);
x_25 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 18, x_25);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__23() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__13;
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__22;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_inlineMatchers___closed__23;
x_3 = l_Lean_Compiler_LCNF_inlineMatchers___closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_inlineMatchers___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__24;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_Lean_Compiler_LCNF_inlineMatchers___closed__20;
x_9 = l_Lean_Compiler_LCNF_inlineMatchers___closed__19;
x_10 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_3);
lean_ctor_set(x_10, 5, x_2);
lean_ctor_set(x_10, 6, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*7, x_8);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 8, x_11);
x_12 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 9, x_12);
x_13 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 10, x_13);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_5 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_6 = lean_st_mk_ref(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed), 6, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_inlineMatchers___lam__2), 6, 0);
x_11 = lean_box(0);
x_12 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
x_13 = lean_unbox(x_11);
x_14 = lean_unbox(x_11);
lean_inc(x_7);
x_15 = l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(x_1, x_10, x_9, x_13, x_14, x_12, x_7, x_2, x_3, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_dec(x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_inlineMatchers___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inlineMatchers___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_inlineMatchers___lam__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_2);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = lean_mk_unsafe_rec_name(x_1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
lean_inc(x_7);
x_11 = l_Lean_Environment_find_x3f(x_7, x_8, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_9);
x_13 = l_Lean_Environment_find_x3f(x_7, x_1, x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = lean_mk_unsafe_rec_name(x_1);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
lean_inc(x_16);
x_20 = l_Lean_Environment_find_x3f(x_16, x_17, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unbox(x_18);
x_22 = l_Lean_Environment_find_x3f(x_16, x_1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_15);
return x_24;
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
lean_dec(x_2);
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
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
lean_dec(x_7);
lean_inc(x_12);
x_14 = lean_is_marked_borrowed(x_12);
x_15 = l_Lean_Compiler_LCNF_mkParam(x_11, x_12, x_14, x_2, x_3, x_4, x_5, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
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
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 2);
lean_inc(x_23);
lean_dec(x_7);
lean_inc(x_22);
x_24 = lean_is_marked_borrowed(x_22);
x_25 = l_Lean_Compiler_LCNF_mkParam(x_21, x_22, x_24, x_2, x_3, x_4, x_5, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_etaExpand(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Meta_mkLambdaFVars(x_3, x_11, x_1, x_2, x_1, x_2, x_14, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_387; lean_object* x_414; 
lean_inc(x_1);
x_414 = lean_is_unsafe_rec_name(x_1);
if (lean_obj_tag(x_414) == 0)
{
x_387 = x_1;
goto block_413;
}
else
{
lean_object* x_415; 
lean_dec(x_1);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
lean_dec(x_414);
x_387 = x_415;
goto block_413;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_ConstantInfo_levelParams(x_9);
lean_dec(x_9);
x_21 = lean_mk_empty_array_with_capacity(x_13);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set_uint8(x_23, sizeof(void*)*6, x_10);
lean_ctor_set_uint8(x_23, sizeof(void*)*6 + 1, x_12);
x_24 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_23, x_15, x_16, x_17, x_18, x_19);
return x_24;
}
block_46:
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_32);
x_34 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_32, x_2, x_3, x_4, x_5, x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_31);
x_39 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_29);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_28);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 1, x_30);
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
x_42 = l_Lean_ConstantInfo_levelParams(x_27);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_31);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_32);
lean_ctor_set(x_44, 3, x_40);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_29);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_28);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_30);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
block_66:
{
lean_object* x_54; uint8_t x_55; 
lean_inc(x_52);
x_54 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_52, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Lean_ConstantInfo_levelParams(x_48);
lean_dec(x_48);
x_58 = l_Lean_Compiler_LCNF_toDecl___closed__1;
x_59 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_52);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_49);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_51);
lean_ctor_set_uint8(x_59, sizeof(void*)*6 + 1, x_50);
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
x_62 = l_Lean_ConstantInfo_levelParams(x_48);
lean_dec(x_48);
x_63 = l_Lean_Compiler_LCNF_toDecl___closed__1;
x_64 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_52);
lean_ctor_set(x_64, 3, x_60);
lean_ctor_set(x_64, 4, x_63);
lean_ctor_set(x_64, 5, x_49);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_51);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 1, x_50);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
block_386:
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_st_ref_get(x_5, x_69);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_67);
lean_inc(x_75);
x_76 = l_Lean_Compiler_getInlineAttribute_x3f(x_75, x_67);
lean_inc(x_67);
lean_inc(x_75);
x_77 = lean_get_extern_attr_data(x_75, x_67);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; lean_object* x_79; 
lean_inc(x_67);
x_78 = l_Lean_hasInitAttr(x_75, x_67);
x_79 = lean_box(1);
if (x_78 == 0)
{
uint8_t x_80; lean_object* x_81; 
x_80 = lean_unbox(x_79);
lean_inc(x_68);
x_81 = l_Lean_ConstantInfo_value_x3f(x_68, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_2);
x_82 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_83 = l_Lean_MessageData_ofName(x_67);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_83);
lean_ctor_set(x_71, 0, x_82);
x_84 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_85, x_3, x_4, x_5, x_74);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint64_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_71);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_box(0);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_91 = lean_st_mk_ref(x_90, x_74);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_ConstantInfo_type(x_68);
x_95 = lean_box(1);
x_96 = lean_box(0);
x_97 = lean_box(2);
x_98 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_98, 0, x_78);
lean_ctor_set_uint8(x_98, 1, x_78);
lean_ctor_set_uint8(x_98, 2, x_78);
lean_ctor_set_uint8(x_98, 3, x_78);
lean_ctor_set_uint8(x_98, 4, x_78);
x_99 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 5, x_99);
x_100 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 6, x_100);
lean_ctor_set_uint8(x_98, 7, x_78);
x_101 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 8, x_101);
x_102 = lean_unbox(x_95);
lean_ctor_set_uint8(x_98, 9, x_102);
x_103 = lean_unbox(x_96);
lean_ctor_set_uint8(x_98, 10, x_103);
x_104 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 11, x_104);
x_105 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 12, x_105);
x_106 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 13, x_106);
x_107 = lean_unbox(x_97);
lean_ctor_set_uint8(x_98, 14, x_107);
x_108 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 15, x_108);
x_109 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 16, x_109);
x_110 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 17, x_110);
x_111 = lean_unbox(x_79);
lean_ctor_set_uint8(x_98, 18, x_111);
x_112 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_98);
x_113 = l_Lean_Compiler_LCNF_inlineMatchers___closed__24;
x_114 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_115 = lean_box(0);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_117, 0, x_98);
lean_ctor_set(x_117, 1, x_88);
lean_ctor_set(x_117, 2, x_113);
lean_ctor_set(x_117, 3, x_114);
lean_ctor_set(x_117, 4, x_115);
lean_ctor_set(x_117, 5, x_89);
lean_ctor_set(x_117, 6, x_116);
lean_ctor_set_uint64(x_117, sizeof(void*)*7, x_112);
lean_ctor_set_uint8(x_117, sizeof(void*)*7 + 8, x_78);
lean_ctor_set_uint8(x_117, sizeof(void*)*7 + 9, x_78);
lean_ctor_set_uint8(x_117, sizeof(void*)*7 + 10, x_78);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_92);
lean_inc(x_117);
x_118 = l_Lean_Compiler_LCNF_toLCNFType(x_94, x_117, x_92, x_4, x_5, x_93);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_box(x_78);
x_122 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(x_122, 0, x_121);
lean_closure_set(x_122, 1, x_79);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_92);
x_123 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_87, x_122, x_78, x_117, x_92, x_4, x_5, x_120);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_5);
lean_inc(x_4);
x_126 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(x_124, x_4, x_5, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_5);
lean_inc(x_4);
x_129 = l_Lean_Compiler_LCNF_macroInline(x_127, x_4, x_5, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_5);
lean_inc(x_4);
x_132 = l_Lean_Compiler_LCNF_inlineMatchers(x_130, x_4, x_5, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_5);
lean_inc(x_4);
x_135 = l_Lean_Compiler_LCNF_macroInline(x_133, x_4, x_5, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_st_ref_get(x_92, x_137);
lean_dec(x_92);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_140 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_136, x_2, x_3, x_4, x_5, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 1)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 5)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
lean_dec(x_141);
x_145 = !lean_is_exclusive(x_142);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_142, 0);
lean_dec(x_146);
x_147 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_144, x_78, x_3, x_143);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_ctor_get(x_144, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_144, 4);
lean_inc(x_150);
lean_dec(x_144);
x_151 = l_Lean_ConstantInfo_levelParams(x_68);
lean_dec(x_68);
lean_ctor_set_tag(x_142, 0);
lean_ctor_set(x_142, 0, x_150);
x_152 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_152, 0, x_67);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_119);
lean_ctor_set(x_152, 3, x_149);
lean_ctor_set(x_152, 4, x_142);
lean_ctor_set(x_152, 5, x_76);
lean_ctor_set_uint8(x_152, sizeof(void*)*6, x_78);
lean_ctor_set_uint8(x_152, sizeof(void*)*6 + 1, x_70);
x_153 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_152, x_2, x_3, x_4, x_5, x_148);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_142);
x_154 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_144, x_78, x_3, x_143);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_ctor_get(x_144, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_144, 4);
lean_inc(x_157);
lean_dec(x_144);
x_158 = l_Lean_ConstantInfo_levelParams(x_68);
lean_dec(x_68);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_157);
x_160 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_160, 0, x_67);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_160, 2, x_119);
lean_ctor_set(x_160, 3, x_156);
lean_ctor_set(x_160, 4, x_159);
lean_ctor_set(x_160, 5, x_76);
lean_ctor_set_uint8(x_160, sizeof(void*)*6, x_78);
lean_ctor_set_uint8(x_160, sizeof(void*)*6 + 1, x_70);
x_161 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_160, x_2, x_3, x_4, x_5, x_155);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_142);
x_162 = lean_ctor_get(x_140, 1);
lean_inc(x_162);
lean_dec(x_140);
x_7 = x_119;
x_8 = x_67;
x_9 = x_68;
x_10 = x_78;
x_11 = x_76;
x_12 = x_70;
x_13 = x_89;
x_14 = x_141;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_162;
goto block_25;
}
}
else
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_140, 1);
lean_inc(x_163);
lean_dec(x_140);
x_7 = x_119;
x_8 = x_67;
x_9 = x_68;
x_10 = x_78;
x_11 = x_76;
x_12 = x_70;
x_13 = x_89;
x_14 = x_141;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_163;
goto block_25;
}
}
else
{
uint8_t x_164; 
lean_dec(x_119);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_140);
if (x_164 == 0)
{
return x_140;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_140, 0);
x_166 = lean_ctor_get(x_140, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_140);
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
lean_dec(x_119);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_135);
if (x_168 == 0)
{
return x_135;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_135, 0);
x_170 = lean_ctor_get(x_135, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_135);
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
lean_dec(x_119);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_172 = !lean_is_exclusive(x_132);
if (x_172 == 0)
{
return x_132;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_132, 0);
x_174 = lean_ctor_get(x_132, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_132);
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
lean_dec(x_119);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_129);
if (x_176 == 0)
{
return x_129;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_129, 0);
x_178 = lean_ctor_get(x_129, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_129);
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
lean_dec(x_119);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_126);
if (x_180 == 0)
{
return x_126;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_126, 0);
x_182 = lean_ctor_get(x_126, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_126);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_119);
lean_dec(x_92);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_123);
if (x_184 == 0)
{
return x_123;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_123, 0);
x_186 = lean_ctor_get(x_123, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_123);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_117);
lean_dec(x_92);
lean_dec(x_87);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_118);
if (x_188 == 0)
{
return x_118;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_118, 0);
x_190 = lean_ctor_get(x_118, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_118);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_free_object(x_71);
x_192 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_193 = lean_st_mk_ref(x_192, x_74);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_ConstantInfo_type(x_68);
x_197 = lean_box(0);
x_198 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_194);
x_199 = l_Lean_Compiler_LCNF_toLCNFType(x_196, x_198, x_194, x_4, x_5, x_195);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_st_ref_get(x_194, x_201);
lean_dec(x_194);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_unbox(x_197);
x_47 = x_67;
x_48 = x_68;
x_49 = x_76;
x_50 = x_70;
x_51 = x_204;
x_52 = x_200;
x_53 = x_203;
goto block_66;
}
else
{
lean_dec(x_194);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_199, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_199, 1);
lean_inc(x_206);
lean_dec(x_199);
x_207 = lean_unbox(x_197);
x_47 = x_67;
x_48 = x_68;
x_49 = x_76;
x_50 = x_70;
x_51 = x_207;
x_52 = x_205;
x_53 = x_206;
goto block_66;
}
else
{
uint8_t x_208; 
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_208 = !lean_is_exclusive(x_199);
if (x_208 == 0)
{
return x_199;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_199, 0);
x_210 = lean_ctor_get(x_199, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_199);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_75);
lean_free_object(x_71);
x_212 = lean_ctor_get(x_77, 0);
lean_inc(x_212);
lean_dec(x_77);
x_213 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_214 = lean_st_mk_ref(x_213, x_74);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lean_ConstantInfo_type(x_68);
x_218 = lean_box(0);
x_219 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_215);
x_220 = l_Lean_Compiler_LCNF_toLCNFType(x_217, x_219, x_215, x_4, x_5, x_216);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_st_ref_get(x_215, x_222);
lean_dec(x_215);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_225 = lean_unbox(x_218);
x_26 = x_67;
x_27 = x_68;
x_28 = x_225;
x_29 = x_76;
x_30 = x_70;
x_31 = x_212;
x_32 = x_221;
x_33 = x_224;
goto block_46;
}
else
{
lean_dec(x_215);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_220, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_220, 1);
lean_inc(x_227);
lean_dec(x_220);
x_228 = lean_unbox(x_218);
x_26 = x_67;
x_27 = x_68;
x_28 = x_228;
x_29 = x_76;
x_30 = x_70;
x_31 = x_212;
x_32 = x_226;
x_33 = x_227;
goto block_46;
}
else
{
uint8_t x_229; 
lean_dec(x_212);
lean_dec(x_76);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_229 = !lean_is_exclusive(x_220);
if (x_229 == 0)
{
return x_220;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_220, 0);
x_231 = lean_ctor_get(x_220, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_220);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_71, 0);
x_234 = lean_ctor_get(x_71, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_71);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
lean_dec(x_233);
lean_inc(x_67);
lean_inc(x_235);
x_236 = l_Lean_Compiler_getInlineAttribute_x3f(x_235, x_67);
lean_inc(x_67);
lean_inc(x_235);
x_237 = lean_get_extern_attr_data(x_235, x_67);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; lean_object* x_239; 
lean_inc(x_67);
x_238 = l_Lean_hasInitAttr(x_235, x_67);
x_239 = lean_box(1);
if (x_238 == 0)
{
uint8_t x_240; lean_object* x_241; 
x_240 = lean_unbox(x_239);
lean_inc(x_68);
x_241 = l_Lean_ConstantInfo_value_x3f(x_68, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_2);
x_242 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_243 = l_Lean_MessageData_ofName(x_67);
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lean_Compiler_LCNF_toDecl___closed__5;
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_246, x_3, x_4, x_5, x_234);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_261; uint8_t x_262; uint8_t x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint64_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_248 = lean_ctor_get(x_241, 0);
lean_inc(x_248);
lean_dec(x_241);
x_249 = lean_box(0);
x_250 = lean_unsigned_to_nat(0u);
x_251 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_252 = lean_st_mk_ref(x_251, x_234);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_ConstantInfo_type(x_68);
x_256 = lean_box(1);
x_257 = lean_box(0);
x_258 = lean_box(2);
x_259 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_259, 0, x_238);
lean_ctor_set_uint8(x_259, 1, x_238);
lean_ctor_set_uint8(x_259, 2, x_238);
lean_ctor_set_uint8(x_259, 3, x_238);
lean_ctor_set_uint8(x_259, 4, x_238);
x_260 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 5, x_260);
x_261 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 6, x_261);
lean_ctor_set_uint8(x_259, 7, x_238);
x_262 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 8, x_262);
x_263 = lean_unbox(x_256);
lean_ctor_set_uint8(x_259, 9, x_263);
x_264 = lean_unbox(x_257);
lean_ctor_set_uint8(x_259, 10, x_264);
x_265 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 11, x_265);
x_266 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 12, x_266);
x_267 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 13, x_267);
x_268 = lean_unbox(x_258);
lean_ctor_set_uint8(x_259, 14, x_268);
x_269 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 15, x_269);
x_270 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 16, x_270);
x_271 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 17, x_271);
x_272 = lean_unbox(x_239);
lean_ctor_set_uint8(x_259, 18, x_272);
x_273 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_259);
x_274 = l_Lean_Compiler_LCNF_inlineMatchers___closed__24;
x_275 = l_Lean_Compiler_LCNF_inlineMatchers___closed__25;
x_276 = lean_box(0);
x_277 = lean_box(0);
x_278 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_278, 0, x_259);
lean_ctor_set(x_278, 1, x_249);
lean_ctor_set(x_278, 2, x_274);
lean_ctor_set(x_278, 3, x_275);
lean_ctor_set(x_278, 4, x_276);
lean_ctor_set(x_278, 5, x_250);
lean_ctor_set(x_278, 6, x_277);
lean_ctor_set_uint64(x_278, sizeof(void*)*7, x_273);
lean_ctor_set_uint8(x_278, sizeof(void*)*7 + 8, x_238);
lean_ctor_set_uint8(x_278, sizeof(void*)*7 + 9, x_238);
lean_ctor_set_uint8(x_278, sizeof(void*)*7 + 10, x_238);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_253);
lean_inc(x_278);
x_279 = l_Lean_Compiler_LCNF_toLCNFType(x_255, x_278, x_253, x_4, x_5, x_254);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_box(x_238);
x_283 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(x_283, 0, x_282);
lean_closure_set(x_283, 1, x_239);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_253);
x_284 = l_Lean_Meta_lambdaTelescope___at_____private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_normalizeAlt_spec__1___redArg(x_248, x_283, x_238, x_278, x_253, x_4, x_5, x_281);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_5);
lean_inc(x_4);
x_287 = l___private_Lean_Compiler_LCNF_ToDecl_0__Lean_Compiler_LCNF_replaceUnsafeRecNames(x_285, x_4, x_5, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
lean_inc(x_5);
lean_inc(x_4);
x_290 = l_Lean_Compiler_LCNF_macroInline(x_288, x_4, x_5, x_289);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
lean_inc(x_5);
lean_inc(x_4);
x_293 = l_Lean_Compiler_LCNF_inlineMatchers(x_291, x_4, x_5, x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
lean_inc(x_5);
lean_inc(x_4);
x_296 = l_Lean_Compiler_LCNF_macroInline(x_294, x_4, x_5, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_st_ref_get(x_253, x_298);
lean_dec(x_253);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec(x_299);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_301 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_297, x_2, x_3, x_4, x_5, x_300);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
if (lean_obj_tag(x_302) == 1)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 5)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
lean_dec(x_301);
x_305 = lean_ctor_get(x_302, 0);
lean_inc(x_305);
lean_dec(x_302);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
x_307 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_305, x_238, x_3, x_304);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
lean_dec(x_307);
x_309 = lean_ctor_get(x_305, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_305, 4);
lean_inc(x_310);
lean_dec(x_305);
x_311 = l_Lean_ConstantInfo_levelParams(x_68);
lean_dec(x_68);
if (lean_is_scalar(x_306)) {
 x_312 = lean_alloc_ctor(0, 1, 0);
} else {
 x_312 = x_306;
 lean_ctor_set_tag(x_312, 0);
}
lean_ctor_set(x_312, 0, x_310);
x_313 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_313, 0, x_67);
lean_ctor_set(x_313, 1, x_311);
lean_ctor_set(x_313, 2, x_280);
lean_ctor_set(x_313, 3, x_309);
lean_ctor_set(x_313, 4, x_312);
lean_ctor_set(x_313, 5, x_236);
lean_ctor_set_uint8(x_313, sizeof(void*)*6, x_238);
lean_ctor_set_uint8(x_313, sizeof(void*)*6 + 1, x_70);
x_314 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_313, x_2, x_3, x_4, x_5, x_308);
return x_314;
}
else
{
lean_object* x_315; 
lean_dec(x_303);
x_315 = lean_ctor_get(x_301, 1);
lean_inc(x_315);
lean_dec(x_301);
x_7 = x_280;
x_8 = x_67;
x_9 = x_68;
x_10 = x_238;
x_11 = x_236;
x_12 = x_70;
x_13 = x_250;
x_14 = x_302;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_315;
goto block_25;
}
}
else
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_301, 1);
lean_inc(x_316);
lean_dec(x_301);
x_7 = x_280;
x_8 = x_67;
x_9 = x_68;
x_10 = x_238;
x_11 = x_236;
x_12 = x_70;
x_13 = x_250;
x_14 = x_302;
x_15 = x_2;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_316;
goto block_25;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_280);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_317 = lean_ctor_get(x_301, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_301, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_319 = x_301;
} else {
 lean_dec_ref(x_301);
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
lean_dec(x_280);
lean_dec(x_253);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_321 = lean_ctor_get(x_296, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_296, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_323 = x_296;
} else {
 lean_dec_ref(x_296);
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
lean_dec(x_280);
lean_dec(x_253);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_325 = lean_ctor_get(x_293, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_293, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_327 = x_293;
} else {
 lean_dec_ref(x_293);
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
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_280);
lean_dec(x_253);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_329 = lean_ctor_get(x_290, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_290, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_331 = x_290;
} else {
 lean_dec_ref(x_290);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_280);
lean_dec(x_253);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_333 = lean_ctor_get(x_287, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_287, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_335 = x_287;
} else {
 lean_dec_ref(x_287);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_280);
lean_dec(x_253);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_337 = lean_ctor_get(x_284, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_284, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_339 = x_284;
} else {
 lean_dec_ref(x_284);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_278);
lean_dec(x_253);
lean_dec(x_248);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_341 = lean_ctor_get(x_279, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_279, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_343 = x_279;
} else {
 lean_dec_ref(x_279);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_345 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_346 = lean_st_mk_ref(x_345, x_234);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = l_Lean_ConstantInfo_type(x_68);
x_350 = lean_box(0);
x_351 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_347);
x_352 = l_Lean_Compiler_LCNF_toLCNFType(x_349, x_351, x_347, x_4, x_5, x_348);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_st_ref_get(x_347, x_354);
lean_dec(x_347);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
x_357 = lean_unbox(x_350);
x_47 = x_67;
x_48 = x_68;
x_49 = x_236;
x_50 = x_70;
x_51 = x_357;
x_52 = x_353;
x_53 = x_356;
goto block_66;
}
else
{
lean_dec(x_347);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_358 = lean_ctor_get(x_352, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_352, 1);
lean_inc(x_359);
lean_dec(x_352);
x_360 = lean_unbox(x_350);
x_47 = x_67;
x_48 = x_68;
x_49 = x_236;
x_50 = x_70;
x_51 = x_360;
x_52 = x_358;
x_53 = x_359;
goto block_66;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_361 = lean_ctor_get(x_352, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_352, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_363 = x_352;
} else {
 lean_dec_ref(x_352);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_235);
x_365 = lean_ctor_get(x_237, 0);
lean_inc(x_365);
lean_dec(x_237);
x_366 = l_Lean_Compiler_LCNF_inlineMatchers___closed__18;
x_367 = lean_st_mk_ref(x_366, x_234);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l_Lean_ConstantInfo_type(x_68);
x_371 = lean_box(0);
x_372 = l_Lean_Compiler_LCNF_inlineMatchers___closed__26;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_368);
x_373 = l_Lean_Compiler_LCNF_toLCNFType(x_370, x_372, x_368, x_4, x_5, x_369);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_st_ref_get(x_368, x_375);
lean_dec(x_368);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
x_378 = lean_unbox(x_371);
x_26 = x_67;
x_27 = x_68;
x_28 = x_378;
x_29 = x_236;
x_30 = x_70;
x_31 = x_365;
x_32 = x_374;
x_33 = x_377;
goto block_46;
}
else
{
lean_dec(x_368);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_379 = lean_ctor_get(x_373, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_373, 1);
lean_inc(x_380);
lean_dec(x_373);
x_381 = lean_unbox(x_371);
x_26 = x_67;
x_27 = x_68;
x_28 = x_381;
x_29 = x_236;
x_30 = x_70;
x_31 = x_365;
x_32 = x_379;
x_33 = x_380;
goto block_46;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_365);
lean_dec(x_236);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_382 = lean_ctor_get(x_373, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_373, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_384 = x_373;
} else {
 lean_dec_ref(x_373);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
}
}
}
block_413:
{
lean_object* x_388; lean_object* x_389; 
lean_inc(x_387);
x_388 = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(x_387, x_5, x_6);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
uint8_t x_390; 
lean_dec(x_2);
x_390 = !lean_is_exclusive(x_388);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_391 = lean_ctor_get(x_388, 1);
x_392 = lean_ctor_get(x_388, 0);
lean_dec(x_392);
x_393 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_394 = l_Lean_MessageData_ofName(x_387);
lean_ctor_set_tag(x_388, 7);
lean_ctor_set(x_388, 1, x_394);
lean_ctor_set(x_388, 0, x_393);
x_395 = l_Lean_Compiler_LCNF_toDecl___closed__7;
x_396 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_396, 0, x_388);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_396, x_3, x_4, x_5, x_391);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_397;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_398 = lean_ctor_get(x_388, 1);
lean_inc(x_398);
lean_dec(x_388);
x_399 = l_Lean_Compiler_LCNF_toDecl___closed__3;
x_400 = l_Lean_MessageData_ofName(x_387);
x_401 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
x_402 = l_Lean_Compiler_LCNF_toDecl___closed__7;
x_403 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_403, x_3, x_4, x_5, x_398);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_404;
}
}
else
{
lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_405 = lean_ctor_get(x_388, 1);
lean_inc(x_405);
lean_dec(x_388);
x_406 = lean_ctor_get(x_389, 0);
lean_inc(x_406);
lean_dec(x_389);
x_407 = l_Lean_ConstantInfo_isPartial(x_406);
if (x_407 == 0)
{
uint8_t x_408; 
x_408 = l_Lean_ConstantInfo_isUnsafe(x_406);
if (x_408 == 0)
{
lean_object* x_409; uint8_t x_410; 
x_409 = lean_box(1);
x_410 = lean_unbox(x_409);
x_67 = x_387;
x_68 = x_406;
x_69 = x_405;
x_70 = x_410;
goto block_386;
}
else
{
x_67 = x_387;
x_68 = x_406;
x_69 = x_405;
x_70 = x_407;
goto block_386;
}
}
else
{
lean_object* x_411; uint8_t x_412; 
x_411 = lean_box(0);
x_412 = lean_unbox(x_411);
x_67 = x_387;
x_68 = x_406;
x_69 = x_405;
x_70 = x_412;
goto block_386;
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_toDecl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Compiler_LCNF_toDecl___lam__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
