// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Congr
// Imports: public import Lean.Meta.Tactic.Simp.Main public import Lean.Meta.Tactic.Congr public import Lean.Elab.Tactic.Conv.Basic
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
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_mkConvGoalFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_markAsConvGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhsRhsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getCongrSimpKindsForArgZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrSimpCore_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshBinderNameForTactic___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Meta_getCongrSimpKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Meta_appendTag(lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isExplicit(lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInfo_getArity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "skip"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(5, 180, 41, 36, 18, 201, 24, 192)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalSkip"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(179, 156, 141, 182, 43, 233, 45, 238)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(88) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__0_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__1_value),((lean_object*)(((size_t)(88) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(95) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__3_value),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "implies_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 71, 54, 187, 9, 73, 178, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "'apply implies_congr' unexpected result"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Elab.Tactic.Conv.Congr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Elab.Tactic.Conv.Congr.0.Lean.Elab.Tactic.Conv.mkCongrThm"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "'congr' conv tactic failed to create congruence theorem"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "invalid `"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "` conv tactic, failed to resolve"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n=\?="};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` conv tactic failed, equality expected"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "invalid 'congr' conv tactic, application or implication expected"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 182, 72, 178, 102, 27, 55, 200)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalCongr"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(223, 20, 53, 193, 93, 21, 59, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(75) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(76) << 1) | 1)),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__1_value),((lean_object*)(((size_t)(64) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(75) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(75) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__4_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arg 0"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "invalid 'arg 0' conv tactic, application expected"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "_private.Lean.Elab.Tactic.Conv.Congr.0.Lean.Elab.Tactic.Conv.mkCongrArgZeroThm"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "` conv tactic failed, cannot select argument"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` conv tactic failed to create congruence theorem"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pi_congr"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 59, 165, 47, 128, 36, 68, 242)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` conv tactic failed, cannot select domain"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "forall_prop_congr_dom"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 60, 41, 113, 120, 179, 141, 84)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Elab.Tactic.Conv.congrArgForall"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__0(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` tactic, application has "};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = " explicit argument(s) but the index is out of bounds"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = " argument(s) but the index is out of bounds"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` conv tactic, index is out of bounds for pi type"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` conv tactic, application or implication expected"};
static const lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_elabArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 63, 45, 128, 216, 102, 81, 96)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_elabArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "argArg"};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 211, 157, 2, 56, 142, 56, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_elabArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "elabArg"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 95, 76, 95, 147, 62, 85, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lhs"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 125, 121, 151, 86, 248, 18, 33)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalLhs"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(36, 180, 193, 203, 66, 121, 65, 51)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(99) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__1_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(97) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 199, 30, 64, 233, 37, 34, 201)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalRhs"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 201, 21, 170, 65, 49, 26, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(101) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(103) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__1_value),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(101) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(101) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid 'fun' conv tactic, application expected"};
static const lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 22, 157, 83, 164, 254, 43, 206)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalFun"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(221, 184, 52, 9, 127, 172, 81, 46)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(48) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__0_value),((lean_object*)(((size_t)(48) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__1_value),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(52) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(131) << 1) | 1)),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__3_value),((lean_object*)(((size_t)(52) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__4_value),((lean_object*)(((size_t)(59) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "failed to go inside let-declaration, type error"};
static const lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "let_body_congr"};
static const lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 115, 150, 132, 106, 100, 45, 219)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "failed to abstract let-expression, result is not type correct"};
static const lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "'apply funext' unexpected result"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "funext"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(226, 251, 226, 140, 5, 134, 146, 130)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(213, 145, 235, 56, 9, 236, 160, 253)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "invalid 'ext' conv tactic, function or arrow expected"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value_aux_3),((lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 59, 213, 100, 231, 162, 190, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evalExt"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(185, 56, 176, 81, 52, 37, 42, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(207) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(213) << 1) | 1)),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__1_value),((lean_object*)(((size_t)(32) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(207) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(207) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "enterArg"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value_aux_3),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 39, 81, 184, 62, 123, 191, 109)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalEnter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_evalEnter___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "enter"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 212, 211, 21, 88, 173, 115, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalEnter"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 213, 99, 98, 130, 128, 15, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 6, 123, 114, 206, 36, 216, 145)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg___boxed(lean_object* v_a_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip(lean_object* v_x_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___boxed(lean_object* v_x_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Elab_Tactic_Conv_evalSkip(v_x_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_x_17_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1(){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_48_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_49_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5));
v___x_50_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8));
v___x_51_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSkip___boxed), 10, 0);
v___x_52_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_48_, v___x_49_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3(){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8));
v___x_82_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6));
v___x_83_ = l_Lean_addBuiltinDeclarationRanges(v___x_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(lean_object* v_msgData_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_toCold_95_; lean_object* v_mctx_96_; lean_object* v_lctx_97_; lean_object* v_options_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_88_);
v_toCold_95_ = lean_ctor_get(v___y_89_, 0);
v_mctx_96_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_mctx_96_);
lean_dec(v___x_94_);
v_lctx_97_ = lean_ctor_get(v___y_87_, 2);
v_options_98_ = lean_ctor_get(v_toCold_95_, 2);
lean_inc_ref(v_options_98_);
lean_inc_ref(v_lctx_97_);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v_env_93_);
lean_ctor_set(v___x_99_, 1, v_mctx_96_);
lean_ctor_set(v___x_99_, 2, v_lctx_97_);
lean_ctor_set(v___x_99_, 3, v_options_98_);
v___x_100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_msgData_86_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0___boxed(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_ref_115_ = lean_ctor_get(v___y_112_, 2);
v___x_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_125_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
lean_inc(v_ref_115_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_ref_115_);
lean_ctor_set(v___x_121_, 1, v_a_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 1);
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg___boxed(lean_object* v_msg_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_132_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object* v_mvarId_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1));
v___x_150_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_149_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2));
v___x_153_ = lean_box(0);
v___x_154_ = l_Lean_MVarId_apply(v_mvarId_143_, v_a_151_, v___x_152_, v___x_153_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
if (lean_obj_tag(v_a_155_) == 1)
{
lean_object* v_tail_163_; 
v_tail_163_ = lean_ctor_get(v_a_155_, 1);
lean_inc(v_tail_163_);
if (lean_obj_tag(v_tail_163_) == 1)
{
lean_object* v_tail_164_; 
v_tail_164_ = lean_ctor_get(v_tail_163_, 1);
lean_inc(v_tail_164_);
if (lean_obj_tag(v_tail_164_) == 1)
{
lean_object* v_tail_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_210_; 
v_tail_165_ = lean_ctor_get(v_tail_164_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_tail_164_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v_tail_164_, 0);
lean_dec(v_unused_211_);
v___x_167_ = v_tail_164_;
v_isShared_168_ = v_isSharedCheck_210_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_tail_165_);
lean_dec(v_tail_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_210_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
if (lean_obj_tag(v_tail_165_) == 1)
{
lean_object* v_tail_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_208_; 
v_tail_169_ = lean_ctor_get(v_tail_165_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_tail_165_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v_tail_165_, 0);
lean_dec(v_unused_209_);
v___x_171_ = v_tail_165_;
v_isShared_172_ = v_isSharedCheck_208_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_tail_169_);
lean_dec(v_tail_165_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_208_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
if (lean_obj_tag(v_tail_169_) == 0)
{
lean_object* v_head_173_; lean_object* v_head_174_; lean_object* v___x_175_; 
v_head_173_ = lean_ctor_get(v_a_155_, 0);
lean_inc(v_head_173_);
lean_dec_ref_known(v_a_155_, 2);
v_head_174_ = lean_ctor_get(v_tail_163_, 0);
lean_inc(v_head_174_);
lean_dec_ref_known(v_tail_163_, 2);
v___x_175_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_173_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_174_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_191_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_191_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_191_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v_a_178_);
v___x_183_ = v___x_171_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_tail_169_);
v___x_183_ = v_reuseFailAlloc_190_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_185_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 1, v___x_183_);
lean_ctor_set(v___x_167_, 0, v_a_176_);
v___x_185_ = v___x_167_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_176_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_183_);
v___x_185_ = v_reuseFailAlloc_189_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_187_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_185_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_a_176_);
lean_del_object(v___x_171_);
lean_del_object(v___x_167_);
v_a_192_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_177_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_177_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_head_174_);
lean_del_object(v___x_171_);
lean_del_object(v___x_167_);
v_a_200_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_175_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_175_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_del_object(v___x_171_);
lean_dec(v_tail_169_);
lean_del_object(v___x_167_);
lean_dec_ref_known(v_tail_163_, 2);
lean_dec_ref_known(v_a_155_, 2);
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
v___y_160_ = v_a_147_;
goto v___jp_156_;
}
}
}
else
{
lean_del_object(v___x_167_);
lean_dec(v_tail_165_);
lean_dec_ref_known(v_tail_163_, 2);
lean_dec_ref_known(v_a_155_, 2);
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
v___y_160_ = v_a_147_;
goto v___jp_156_;
}
}
}
else
{
lean_dec_ref_known(v_tail_163_, 2);
lean_dec(v_tail_164_);
lean_dec_ref_known(v_a_155_, 2);
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
v___y_160_ = v_a_147_;
goto v___jp_156_;
}
}
else
{
lean_dec_ref_known(v_a_155_, 2);
lean_dec(v_tail_163_);
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
v___y_160_ = v_a_147_;
goto v___jp_156_;
}
}
else
{
lean_dec(v_a_155_);
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
v___y_160_ = v_a_147_;
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4);
v___x_162_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_161_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
return v___x_162_;
}
}
else
{
return v___x_154_;
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_mvarId_143_);
v_a_212_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_150_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_150_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object* v_mvarId_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object* v_00_u03b1_227_, lean_object* v_msg_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(v_00_u03b1_235_, v_msg_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object* v_e_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Expr_isArrow(v_e_243_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_box(v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = l_Lean_Expr_bindingDomain_x21(v_e_243_);
v___x_253_ = l_Lean_Meta_isProp(v___x_252_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; uint8_t v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
v___x_255_ = lean_unbox(v_a_254_);
lean_dec(v_a_254_);
if (v___x_255_ == 0)
{
return v___x_253_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref_known(v___x_253_, 1);
v___x_256_ = l_Lean_Expr_bindingBody_x21(v_e_243_);
v___x_257_ = l_Lean_Meta_isProp(v___x_256_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
return v___x_257_;
}
}
else
{
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object* v_e_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v_e_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec_ref(v_e_258_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___f_272_; lean_object* v___x_8170__overap_273_; lean_object* v___x_274_; 
v___f_272_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_8170__overap_273_ = lean_panic_fn_borrowed(v___f_272_, v_msg_266_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
v___x_274_ = lean_apply_5(v___x_8170__overap_273_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, lean_box(0));
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___boxed(lean_object* v_msg_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v_msg_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(lean_object* v___x_282_, lean_object* v_fst_283_, lean_object* v_fst_284_, lean_object* v_fst_285_, lean_object* v_snd_286_, lean_object* v_tag_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
lean_inc_ref(v___x_282_);
v___x_293_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_282_, v_tag_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_318_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_318_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_318_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_318_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_fst_298_; lean_object* v_snd_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_317_; 
v_fst_298_ = lean_ctor_get(v_a_294_, 0);
v_snd_299_ = lean_ctor_get(v_a_294_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_a_294_);
if (v_isSharedCheck_317_ == 0)
{
v___x_301_ = v_a_294_;
v_isShared_302_ = v_isSharedCheck_317_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_snd_299_);
lean_inc(v_fst_298_);
lean_dec(v_a_294_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_317_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
lean_inc(v_fst_298_);
v___x_303_ = l_Lean_Expr_app___override(v_fst_283_, v_fst_298_);
lean_inc(v_snd_299_);
v___x_304_ = l_Lean_mkApp3(v_fst_284_, v___x_282_, v_fst_298_, v_snd_299_);
v___x_305_ = l_Lean_Expr_mvarId_x21(v_snd_299_);
lean_dec(v_snd_299_);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
v___x_307_ = lean_array_push(v_fst_285_, v___x_306_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v_snd_286_);
lean_ctor_set(v___x_301_, 0, v___x_307_);
v___x_309_ = v___x_301_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_snd_286_);
v___x_309_ = v_reuseFailAlloc_316_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_304_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_303_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_312_);
v___x_314_ = v___x_296_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_snd_286_);
lean_dec(v_fst_285_);
lean_dec(v_fst_284_);
lean_dec(v_fst_283_);
lean_dec_ref(v___x_282_);
v_a_319_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_293_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_293_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1___boxed(lean_object* v___x_327_, lean_object* v_fst_328_, lean_object* v_fst_329_, lean_object* v_fst_330_, lean_object* v_snd_331_, lean_object* v_tag_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_327_, v_fst_328_, v_fst_329_, v_fst_330_, v_snd_331_, v_tag_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_342_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_343_ = lean_unsigned_to_nat(30u);
v___x_344_ = lean_unsigned_to_nat(68u);
v___x_345_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1));
v___x_346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_347_ = l_mkPanicMessageWithDecl(v___x_346_, v___x_345_, v___x_344_, v___x_343_, v___x_342_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(lean_object* v_fst_348_, lean_object* v_snd_349_, lean_object* v_fst_350_, lean_object* v_fst_351_, lean_object* v_00___352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3);
v___x_359_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_358_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_370_; 
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_359_, 0);
lean_dec(v_unused_371_);
v___x_361_ = v___x_359_;
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
else
{
lean_dec(v___x_359_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_370_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_fst_348_);
lean_ctor_set(v___x_363_, 1, v_snd_349_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_fst_350_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_fst_351_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_366_);
v___x_368_ = v___x_361_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
lean_dec(v_fst_351_);
lean_dec(v_fst_350_);
lean_dec(v_snd_349_);
lean_dec(v_fst_348_);
v_a_372_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_359_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_359_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___boxed(lean_object* v_fst_380_, lean_object* v_snd_381_, lean_object* v_fst_382_, lean_object* v_fst_383_, lean_object* v_00___384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_380_, v_snd_381_, v_fst_382_, v_fst_383_, v_00___384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(lean_object* v_upperBound_391_, lean_object* v_args_392_, uint8_t v_nameSubgoals_393_, lean_object* v_origTag_394_, lean_object* v_a_395_, lean_object* v___x_396_, uint8_t v_addImplicitArgs_397_, lean_object* v_a_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_a_406_; lean_object* v___y_411_; uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_lt(v_a_398_, v_upperBound_391_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_399_);
return v___x_431_;
}
else
{
lean_object* v_snd_432_; lean_object* v_snd_433_; lean_object* v_fst_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_575_; 
v_snd_432_ = lean_ctor_get(v_b_399_, 1);
lean_inc(v_snd_432_);
v_snd_433_ = lean_ctor_get(v_snd_432_, 1);
lean_inc(v_snd_433_);
v_fst_434_ = lean_ctor_get(v_b_399_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_b_399_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_b_399_, 1);
lean_dec(v_unused_576_);
v___x_436_ = v_b_399_;
v_isShared_437_ = v_isSharedCheck_575_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_fst_434_);
lean_dec(v_b_399_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_575_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_fst_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_573_; 
v_fst_438_ = lean_ctor_get(v_snd_432_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_snd_432_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_snd_432_, 1);
lean_dec(v_unused_574_);
v___x_440_ = v_snd_432_;
v_isShared_441_ = v_isSharedCheck_573_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_fst_438_);
lean_dec(v_snd_432_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_573_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_fst_442_; lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_572_; 
v_fst_442_ = lean_ctor_get(v_snd_433_, 0);
v_snd_443_ = lean_ctor_get(v_snd_433_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_snd_433_);
if (v_isSharedCheck_572_ == 0)
{
v___x_445_ = v_snd_433_;
v_isShared_446_ = v_isSharedCheck_572_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snd_443_);
lean_inc(v_fst_442_);
lean_dec(v_snd_433_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_572_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v_paramInfo_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_paramInfo_447_ = lean_ctor_get(v_a_395_, 0);
v___x_448_ = l_Lean_instInhabitedExpr;
v___x_449_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_450_ = lean_array_get_borrowed(v___x_448_, v_args_392_, v_a_398_);
v___x_451_ = lean_array_get_borrowed(v___x_449_, v_paramInfo_447_, v_a_398_);
v___x_452_ = lean_array_fget_borrowed(v___x_396_, v_a_398_);
v___x_453_ = lean_unbox(v___x_452_);
switch(v___x_453_)
{
case 1:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_del_object(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
v___x_454_ = lean_box(0);
v___x_455_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_442_, v_snd_443_, v_fst_438_, v_fst_434_, v___x_454_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
v___y_411_ = v___x_455_;
goto v___jp_410_;
}
case 2:
{
if (v_addImplicitArgs_397_ == 0)
{
uint8_t v___x_481_; 
v___x_481_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_451_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
lean_inc_n(v___x_450_, 2);
v___x_482_ = l_Lean_Expr_app___override(v_fst_434_, v___x_450_);
v___x_483_ = l_Lean_Meta_mkEqRefl(v___x_450_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
lean_inc_n(v___x_450_, 2);
v___x_485_ = l_Lean_mkApp3(v_fst_438_, v___x_450_, v___x_450_, v_a_484_);
if (v_isShared_446_ == 0)
{
v___x_487_ = v___x_445_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_fst_442_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_snd_443_);
v___x_487_ = v_reuseFailAlloc_494_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_487_);
lean_ctor_set(v___x_440_, 0, v___x_485_);
v___x_489_ = v___x_440_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_489_);
lean_ctor_set(v___x_436_, 0, v___x_482_);
v___x_491_ = v___x_436_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
v_a_406_ = v___x_491_;
goto v___jp_405_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v___x_482_);
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
lean_dec(v_fst_442_);
lean_del_object(v___x_440_);
lean_dec(v_fst_438_);
lean_del_object(v___x_436_);
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_495_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_483_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_483_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_del_object(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_456_;
}
}
else
{
lean_del_object(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
goto v___jp_456_;
}
v___jp_456_:
{
if (v_nameSubgoals_393_ == 0)
{
lean_object* v___x_457_; 
lean_inc(v_origTag_394_);
lean_inc(v___x_450_);
v___x_457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_450_, v_fst_434_, v_fst_438_, v_fst_442_, v_snd_443_, v_origTag_394_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
v___y_411_ = v___x_457_;
goto v___jp_410_;
}
else
{
lean_object* v___x_458_; 
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc(v_fst_438_);
v___x_458_ = lean_infer_type(v_fst_438_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
v___x_460_ = lean_whnf(v_a_459_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
v___x_462_ = l_Lean_Expr_bindingName_x21(v_a_461_);
lean_dec(v_a_461_);
lean_inc(v_origTag_394_);
v___x_463_ = l_Lean_Meta_appendTag(v_origTag_394_, v___x_462_);
lean_dec(v___x_462_);
lean_inc(v___x_450_);
v___x_464_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_450_, v_fst_434_, v_fst_438_, v_fst_442_, v_snd_443_, v___x_463_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
v___y_411_ = v___x_464_;
goto v___jp_410_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_snd_443_);
lean_dec(v_fst_442_);
lean_dec(v_fst_438_);
lean_dec(v_fst_434_);
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_465_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_460_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_460_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_snd_443_);
lean_dec(v_fst_442_);
lean_dec(v_fst_438_);
lean_dec(v_fst_434_);
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_473_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_458_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_458_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_del_object(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
v___x_503_ = lean_box(0);
v___x_504_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_442_, v_snd_443_, v_fst_438_, v_fst_434_, v___x_503_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
v___y_411_ = v___x_504_;
goto v___jp_410_;
}
case 5:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_inc(v___x_450_);
v___x_505_ = l_Lean_Expr_app___override(v_fst_438_, v___x_450_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
lean_inc_ref(v___x_505_);
v___x_506_ = lean_infer_type(v___x_505_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v___y_401_);
lean_inc_ref(v___y_400_);
v___x_508_ = lean_whnf(v_a_507_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = l_Lean_Expr_bindingDomain_x21(v_a_509_);
lean_dec(v_a_509_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
v___x_512_ = 0;
v___x_513_ = lean_box(0);
v___x_514_ = l_Lean_Meta_mkFreshExprMVar(v___x_511_, v___x_512_, v___x_513_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc_n(v_a_515_, 3);
lean_dec_ref_known(v___x_514_, 1);
v___x_516_ = l_Lean_Expr_app___override(v_fst_434_, v_a_515_);
v___x_517_ = l_Lean_Expr_app___override(v___x_505_, v_a_515_);
v___x_518_ = l_Lean_Expr_mvarId_x21(v_a_515_);
lean_dec(v_a_515_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
v___x_520_ = lean_array_push(v_snd_443_, v___x_519_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_520_);
v___x_522_ = v___x_445_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_fst_442_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_529_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_522_);
lean_ctor_set(v___x_440_, 0, v___x_517_);
v___x_524_ = v___x_440_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_524_);
lean_ctor_set(v___x_436_, 0, v___x_516_);
v___x_526_ = v___x_436_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v_a_406_ = v___x_526_;
goto v___jp_405_;
}
}
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec_ref(v___x_505_);
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
lean_dec(v_fst_442_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_530_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_514_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_514_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v___x_505_);
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
lean_dec(v_fst_442_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_538_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_508_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_508_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
lean_dec_ref(v___x_505_);
lean_del_object(v___x_445_);
lean_dec(v_snd_443_);
lean_dec(v_fst_442_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_546_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_506_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_506_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
default: 
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc_n(v___x_450_, 2);
v___x_554_ = l_Lean_Expr_app___override(v_fst_434_, v___x_450_);
v___x_555_ = l_Lean_Expr_app___override(v_fst_438_, v___x_450_);
if (v_addImplicitArgs_397_ == 0)
{
uint8_t v___x_568_; 
v___x_568_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_451_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_del_object(v___x_445_);
lean_del_object(v___x_440_);
lean_del_object(v___x_436_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_fst_442_);
lean_ctor_set(v___x_569_, 1, v_snd_443_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_555_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_554_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v_a_406_ = v___x_571_;
goto v___jp_405_;
}
else
{
goto v___jp_556_;
}
}
else
{
goto v___jp_556_;
}
v___jp_556_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_557_ = lean_box(0);
v___x_558_ = lean_array_push(v_fst_442_, v___x_557_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_558_);
v___x_560_ = v___x_445_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_snd_443_);
v___x_560_ = v_reuseFailAlloc_567_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_560_);
lean_ctor_set(v___x_440_, 0, v___x_555_);
v___x_562_ = v___x_440_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_560_);
v___x_562_ = v_reuseFailAlloc_566_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_564_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_562_);
lean_ctor_set(v___x_436_, 0, v___x_554_);
v___x_564_ = v___x_436_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v_a_406_ = v___x_564_;
goto v___jp_405_;
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
v___jp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_add(v_a_398_, v___x_407_);
lean_dec(v_a_398_);
v_a_398_ = v___x_408_;
v_b_399_ = v_a_406_;
goto _start;
}
v___jp_410_:
{
if (lean_obj_tag(v___y_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_421_; 
v_a_412_ = lean_ctor_get(v___y_411_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___y_411_);
if (v_isSharedCheck_421_ == 0)
{
v___x_414_ = v___y_411_;
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___y_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_421_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
if (lean_obj_tag(v_a_412_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; 
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_416_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_a_416_);
lean_dec_ref_known(v_a_412_, 1);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v_a_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v_a_420_; 
lean_del_object(v___x_414_);
v_a_420_ = lean_ctor_get(v_a_412_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v_a_412_, 1);
v_a_406_ = v_a_420_;
goto v___jp_405_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_a_398_);
lean_dec(v_origTag_394_);
v_a_422_ = lean_ctor_get(v___y_411_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___y_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___y_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___y_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___boxed(lean_object* v_upperBound_577_, lean_object* v_args_578_, lean_object* v_nameSubgoals_579_, lean_object* v_origTag_580_, lean_object* v_a_581_, lean_object* v___x_582_, lean_object* v_addImplicitArgs_583_, lean_object* v_a_584_, lean_object* v_b_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v_nameSubgoals_boxed_591_; uint8_t v_addImplicitArgs_boxed_592_; lean_object* v_res_593_; 
v_nameSubgoals_boxed_591_ = lean_unbox(v_nameSubgoals_579_);
v_addImplicitArgs_boxed_592_ = lean_unbox(v_addImplicitArgs_583_);
v_res_593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_577_, v_args_578_, v_nameSubgoals_boxed_591_, v_origTag_580_, v_a_581_, v___x_582_, v_addImplicitArgs_boxed_592_, v_a_584_, v_b_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec_ref(v___x_582_);
lean_dec_ref(v_a_581_);
lean_dec_ref(v_args_578_);
lean_dec(v_upperBound_577_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(lean_object* v_a_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_array_601_; lean_object* v_start_602_; lean_object* v_stop_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_618_; 
v_array_601_ = lean_ctor_get(v_a_594_, 0);
v_start_602_ = lean_ctor_get(v_a_594_, 1);
v_stop_603_ = lean_ctor_get(v_a_594_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_a_594_);
if (v_isSharedCheck_618_ == 0)
{
v___x_605_ = v_a_594_;
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_stop_603_);
lean_inc(v_start_602_);
lean_inc(v_array_601_);
lean_dec(v_a_594_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_618_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
uint8_t v___x_607_; 
v___x_607_ = lean_nat_dec_lt(v_start_602_, v_stop_603_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
lean_del_object(v___x_605_);
lean_dec(v_stop_603_);
lean_dec(v_start_602_);
lean_dec_ref(v_array_601_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v_b_595_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_array_fget_borrowed(v_array_601_, v_start_602_);
lean_inc(v___x_609_);
v___x_610_ = l_Lean_Meta_mkCongrFun(v_b_595_, v___x_609_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_add(v_start_602_, v___x_612_);
lean_dec(v_start_602_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_613_);
v___x_615_ = v___x_605_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_array_601_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_stop_603_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v_a_594_ = v___x_615_;
v_b_595_ = v_a_611_;
goto _start;
}
}
else
{
lean_del_object(v___x_605_);
lean_dec(v_stop_603_);
lean_dec(v_start_602_);
lean_dec_ref(v_array_601_);
return v___x_610_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg___boxed(lean_object* v_a_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_619_, v_b_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
return v_res_626_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(lean_object* v_origTag_634_, lean_object* v_f_635_, lean_object* v_args_636_, uint8_t v_addImplicitArgs_637_, uint8_t v_nameSubgoals_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_proof_645_; lean_object* v_mvarIdsNew_646_; lean_object* v_mvarIdsNewInsts_647_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_array_get_size(v_args_636_);
lean_inc_ref(v_f_635_);
v___x_652_ = l_Lean_Meta_getFunInfoNArgs(v_f_635_, v___x_651_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
lean_inc_ref(v_f_635_);
v___x_654_ = l_Lean_Meta_getCongrSimpKinds(v_f_635_, v_a_653_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; uint8_t v___x_656_; lean_object* v___x_657_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = 0;
lean_inc(v_a_653_);
lean_inc_ref(v_f_635_);
v___x_657_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_635_, v_a_653_, v_a_655_, v___x_656_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
if (lean_obj_tag(v_a_658_) == 1)
{
lean_object* v_val_659_; lean_object* v_proof_660_; lean_object* v_argKinds_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_val_659_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_val_659_);
lean_dec_ref_known(v_a_658_, 1);
v_proof_660_ = lean_ctor_get(v_val_659_, 1);
lean_inc_ref(v_proof_660_);
v_argKinds_661_ = lean_ctor_get(v_val_659_, 2);
lean_inc_ref(v_argKinds_661_);
lean_dec(v_val_659_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_array_get_size(v_argKinds_661_);
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1));
v___x_665_ = lean_nat_dec_lt(v___x_663_, v___x_651_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_proof_660_);
lean_ctor_set(v___x_666_, 1, v___x_664_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_f_635_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
lean_inc(v_origTag_634_);
v___x_668_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v___x_663_, v_args_636_, v_nameSubgoals_638_, v_origTag_634_, v_a_653_, v_argKinds_661_, v_addImplicitArgs_637_, v___x_662_, v___x_667_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
lean_dec_ref(v_argKinds_661_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_snd_670_; lean_object* v_snd_671_; lean_object* v_fst_672_; lean_object* v_fst_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v_lower_681_; lean_object* v_upper_682_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v_snd_670_ = lean_ctor_get(v_a_669_, 1);
lean_inc(v_snd_670_);
v_snd_671_ = lean_ctor_get(v_snd_670_, 1);
lean_inc(v_snd_671_);
v_fst_672_ = lean_ctor_get(v_a_669_, 0);
lean_inc(v_fst_672_);
lean_dec(v_a_669_);
v_fst_673_ = lean_ctor_get(v_snd_670_, 0);
lean_inc(v_fst_673_);
lean_dec(v_snd_670_);
v_fst_674_ = lean_ctor_get(v_snd_671_, 0);
lean_inc(v_fst_674_);
v_snd_675_ = lean_ctor_get(v_snd_671_, 1);
lean_inc(v_snd_675_);
lean_dec(v_snd_671_);
if (v___x_665_ == 0)
{
lean_dec(v_fst_672_);
lean_dec(v_a_653_);
lean_dec_ref(v_args_636_);
lean_dec(v_origTag_634_);
v_proof_645_ = v_fst_673_;
v_mvarIdsNew_646_ = v_fst_674_;
v_mvarIdsNewInsts_647_ = v_snd_675_;
goto v___jp_644_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_eq(v___x_663_, v___x_662_);
if (v___x_720_ == 0)
{
v___y_714_ = v_a_639_;
v___y_715_ = v_a_640_;
v___y_716_ = v_a_641_;
v___y_717_ = v_a_642_;
goto v___jp_713_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_722_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_721_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_dec_ref_known(v___x_722_, 1);
v___y_714_ = v_a_639_;
v___y_715_ = v_a_640_;
v___y_716_ = v_a_641_;
v___y_717_ = v_a_642_;
goto v___jp_713_;
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v_snd_675_);
lean_dec(v_fst_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_672_);
lean_dec(v_a_653_);
lean_dec_ref(v_args_636_);
lean_dec(v_origTag_634_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
v___jp_676_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = l_Array_toSubarray___redArg(v_args_636_, v_lower_681_, v_upper_682_);
lean_inc_ref(v___x_683_);
v___x_684_ = l_Subarray_copy___redArg(v___x_683_);
v___x_685_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_634_, v_fst_672_, v___x_684_, v_addImplicitArgs_637_, v_nameSubgoals_638_, v___y_679_, v___y_677_, v___y_680_, v___y_678_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v_snd_687_; lean_object* v_fst_688_; lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___x_691_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v_snd_687_ = lean_ctor_get(v_a_686_, 1);
lean_inc(v_snd_687_);
v_fst_688_ = lean_ctor_get(v_a_686_, 0);
lean_inc(v_fst_688_);
lean_dec(v_a_686_);
v_fst_689_ = lean_ctor_get(v_snd_687_, 0);
lean_inc(v_fst_689_);
v_snd_690_ = lean_ctor_get(v_snd_687_, 1);
lean_inc(v_snd_690_);
lean_dec(v_snd_687_);
v___x_691_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_683_, v_fst_673_, v___y_679_, v___y_677_, v___y_680_, v___y_678_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = l_Lean_Meta_mkEqTrans(v_a_692_, v_fst_688_, v___y_679_, v___y_677_, v___y_680_, v___y_678_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = l_Array_append___redArg(v_fst_674_, v_fst_689_);
lean_dec(v_fst_689_);
v___x_696_ = l_Array_append___redArg(v_snd_675_, v_snd_690_);
lean_dec(v_snd_690_);
v_proof_645_ = v_a_694_;
v_mvarIdsNew_646_ = v___x_695_;
v_mvarIdsNewInsts_647_ = v___x_696_;
goto v___jp_644_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_snd_690_);
lean_dec(v_fst_689_);
lean_dec(v_snd_675_);
lean_dec(v_fst_674_);
v_a_697_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_693_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_snd_690_);
lean_dec(v_fst_689_);
lean_dec(v_fst_688_);
lean_dec(v_snd_675_);
lean_dec(v_fst_674_);
v_a_705_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_691_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_691_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
else
{
lean_dec_ref(v___x_683_);
lean_dec(v_snd_675_);
lean_dec(v_fst_674_);
lean_dec(v_fst_673_);
return v___x_685_;
}
}
v___jp_713_:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Meta_FunInfo_getArity(v_a_653_);
lean_dec(v_a_653_);
v___x_719_ = lean_nat_dec_le(v___x_718_, v___x_662_);
if (v___x_719_ == 0)
{
v___y_677_ = v___y_715_;
v___y_678_ = v___y_717_;
v___y_679_ = v___y_714_;
v___y_680_ = v___y_716_;
v_lower_681_ = v___x_718_;
v_upper_682_ = v___x_651_;
goto v___jp_676_;
}
else
{
lean_dec(v___x_718_);
v___y_677_ = v___y_715_;
v___y_678_ = v___y_717_;
v___y_679_ = v___y_714_;
v___y_680_ = v___y_716_;
v_lower_681_ = v___x_662_;
v_upper_682_ = v___x_651_;
goto v___jp_676_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_a_653_);
lean_dec_ref(v_args_636_);
lean_dec(v_origTag_634_);
v_a_731_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_668_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_668_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v_a_658_);
lean_dec(v_a_653_);
lean_dec_ref(v_args_636_);
lean_dec_ref(v_f_635_);
lean_dec(v_origTag_634_);
v___x_739_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_740_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_739_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_740_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_653_);
lean_dec_ref(v_args_636_);
lean_dec_ref(v_f_635_);
lean_dec(v_origTag_634_);
v_a_741_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_657_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_657_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_653_);
lean_dec_ref(v_args_636_);
lean_dec_ref(v_f_635_);
lean_dec(v_origTag_634_);
v_a_749_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_654_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_654_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v_args_636_);
lean_dec_ref(v_f_635_);
lean_dec(v_origTag_634_);
v_a_757_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_652_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_652_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
v___jp_644_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_mvarIdsNew_646_);
lean_ctor_set(v___x_648_, 1, v_mvarIdsNewInsts_647_);
v___x_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_649_, 0, v_proof_645_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___boxed(lean_object* v_origTag_765_, lean_object* v_f_766_, lean_object* v_args_767_, lean_object* v_addImplicitArgs_768_, lean_object* v_nameSubgoals_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
uint8_t v_addImplicitArgs_boxed_775_; uint8_t v_nameSubgoals_boxed_776_; lean_object* v_res_777_; 
v_addImplicitArgs_boxed_775_ = lean_unbox(v_addImplicitArgs_768_);
v_nameSubgoals_boxed_776_ = lean_unbox(v_nameSubgoals_769_);
v_res_777_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_765_, v_f_766_, v_args_767_, v_addImplicitArgs_boxed_775_, v_nameSubgoals_boxed_776_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_object* v_inst_778_, lean_object* v_R_779_, lean_object* v_a_780_, lean_object* v_b_781_, lean_object* v_c_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_780_, v_b_781_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___boxed(lean_object* v_inst_789_, lean_object* v_R_790_, lean_object* v_a_791_, lean_object* v_b_792_, lean_object* v_c_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(v_inst_789_, v_R_790_, v_a_791_, v_b_792_, v_c_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(lean_object* v_upperBound_800_, lean_object* v_args_801_, uint8_t v_nameSubgoals_802_, lean_object* v_origTag_803_, lean_object* v_a_804_, lean_object* v___x_805_, uint8_t v_addImplicitArgs_806_, lean_object* v_inst_807_, lean_object* v_R_808_, lean_object* v_a_809_, lean_object* v_b_810_, lean_object* v_c_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_800_, v_args_801_, v_nameSubgoals_802_, v_origTag_803_, v_a_804_, v___x_805_, v_addImplicitArgs_806_, v_a_809_, v_b_810_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_818_ = _args[0];
lean_object* v_args_819_ = _args[1];
lean_object* v_nameSubgoals_820_ = _args[2];
lean_object* v_origTag_821_ = _args[3];
lean_object* v_a_822_ = _args[4];
lean_object* v___x_823_ = _args[5];
lean_object* v_addImplicitArgs_824_ = _args[6];
lean_object* v_inst_825_ = _args[7];
lean_object* v_R_826_ = _args[8];
lean_object* v_a_827_ = _args[9];
lean_object* v_b_828_ = _args[10];
lean_object* v_c_829_ = _args[11];
lean_object* v___y_830_ = _args[12];
lean_object* v___y_831_ = _args[13];
lean_object* v___y_832_ = _args[14];
lean_object* v___y_833_ = _args[15];
lean_object* v___y_834_ = _args[16];
_start:
{
uint8_t v_nameSubgoals_boxed_835_; uint8_t v_addImplicitArgs_boxed_836_; lean_object* v_res_837_; 
v_nameSubgoals_boxed_835_ = lean_unbox(v_nameSubgoals_820_);
v_addImplicitArgs_boxed_836_ = lean_unbox(v_addImplicitArgs_824_);
v_res_837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(v_upperBound_818_, v_args_819_, v_nameSubgoals_boxed_835_, v_origTag_821_, v_a_822_, v___x_823_, v_addImplicitArgs_boxed_836_, v_inst_825_, v_R_826_, v_a_827_, v_b_828_, v_c_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v___x_823_);
lean_dec_ref(v_a_822_);
lean_dec_ref(v_args_819_);
lean_dec(v_upperBound_818_);
return v_res_837_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2));
v___x_843_ = l_Lean_stringToMessageData(v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(lean_object* v_tacticName_847_, lean_object* v_rhs_848_, lean_object* v_rhs_x27_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v___x_855_; 
lean_inc_ref(v_rhs_x27_849_);
lean_inc_ref(v_rhs_848_);
v___x_855_ = l_Lean_Meta_isExprDefEqGuarded(v_rhs_848_, v_rhs_x27_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_877_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_877_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_877_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_877_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint8_t v___x_860_; 
v___x_860_ = lean_unbox(v_a_856_);
lean_dec(v_a_856_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_del_object(v___x_858_);
v___x_861_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_862_ = l_Lean_stringToMessageData(v_tacticName_847_);
v___x_863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_861_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = l_Lean_indentExpr(v_rhs_848_);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = l_Lean_indentExpr(v_rhs_x27_849_);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_871_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_875_; 
lean_dec_ref(v_rhs_x27_849_);
lean_dec_ref(v_rhs_848_);
lean_dec_ref(v_tacticName_847_);
v___x_873_ = lean_box(0);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_873_);
v___x_875_ = v___x_858_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v_rhs_x27_849_);
lean_dec_ref(v_rhs_848_);
lean_dec_ref(v_tacticName_847_);
v_a_878_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_855_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_855_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___boxed(lean_object* v_tacticName_886_, lean_object* v_rhs_887_, lean_object* v_rhs_x27_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_886_, v_rhs_887_, v_rhs_x27_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_894_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2));
v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4));
v___x_903_ = l_Lean_stringToMessageData(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(lean_object* v_tacticName_904_, lean_object* v_rhs_905_, lean_object* v_proof_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; 
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc_ref(v_a_907_);
v___x_912_ = lean_infer_type(v_proof_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
lean_inc(v_a_908_);
lean_inc_ref(v_a_907_);
v___x_914_ = lean_whnf(v_a_913_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1));
v___x_917_ = lean_unsigned_to_nat(3u);
v___x_918_ = l_Lean_Expr_isAppOfArity(v_a_915_, v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_a_915_);
lean_dec_ref(v_rhs_905_);
v___x_919_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_920_ = l_Lean_stringToMessageData(v_tacticName_904_);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_923_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = l_Lean_Expr_appArg_x21(v_a_915_);
lean_dec(v_a_915_);
v___x_926_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_904_, v_rhs_905_, v___x_925_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
return v___x_926_;
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_rhs_905_);
lean_dec_ref(v_tacticName_904_);
v_a_927_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_914_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_914_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_rhs_905_);
lean_dec_ref(v_tacticName_904_);
v_a_935_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_912_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_912_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___boxed(lean_object* v_tacticName_943_, lean_object* v_rhs_944_, lean_object* v_proof_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_943_, v_rhs_944_, v_proof_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(lean_object* v_e_952_, lean_object* v___y_953_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Expr_hasMVar(v_e_952_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_956_, 0, v_e_952_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; lean_object* v_mctx_958_; lean_object* v___x_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_962_; lean_object* v_cache_963_; lean_object* v_zetaDeltaFVarIds_964_; lean_object* v_postponed_965_; lean_object* v_diag_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_975_; 
v___x_957_ = lean_st_ref_get(v___y_953_);
v_mctx_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc_ref(v_mctx_958_);
lean_dec(v___x_957_);
v___x_959_ = l_Lean_instantiateMVarsCore(v_mctx_958_, v_e_952_);
v_fst_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v___x_959_, 1);
lean_inc(v_snd_961_);
lean_dec_ref(v___x_959_);
v___x_962_ = lean_st_ref_take(v___y_953_);
v_cache_963_ = lean_ctor_get(v___x_962_, 1);
v_zetaDeltaFVarIds_964_ = lean_ctor_get(v___x_962_, 2);
v_postponed_965_ = lean_ctor_get(v___x_962_, 3);
v_diag_966_ = lean_ctor_get(v___x_962_, 4);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_976_);
v___x_968_ = v___x_962_;
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_diag_966_);
lean_inc(v_postponed_965_);
lean_inc(v_zetaDeltaFVarIds_964_);
lean_inc(v_cache_963_);
lean_dec(v___x_962_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_975_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v_snd_961_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_snd_961_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_cache_963_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_zetaDeltaFVarIds_964_);
lean_ctor_set(v_reuseFailAlloc_974_, 3, v_postponed_965_);
lean_ctor_set(v_reuseFailAlloc_974_, 4, v_diag_966_);
v___x_971_ = v_reuseFailAlloc_974_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_st_ref_put(v___y_953_, v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_fst_960_);
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg___boxed(lean_object* v_e_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_977_, v___y_978_);
lean_dec(v___y_978_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(lean_object* v_e_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_981_, v___y_983_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___boxed(lean_object* v_e_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(v_e_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(lean_object* v_mvarId_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_995_, v_x_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1002_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1002_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg___boxed(lean_object* v_mvarId_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1019_, v_x_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_object* v_00_u03b1_1027_, lean_object* v_mvarId_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1028_, v_x_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_mvarId_1037_, lean_object* v_x_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(v_00_u03b1_1036_, v_mvarId_1037_, v_x_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
if (lean_obj_tag(v_a_1045_) == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = l_List_reverse___redArg(v_a_1046_);
return v___x_1047_;
}
else
{
lean_object* v_head_1048_; lean_object* v_tail_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1058_; 
v_head_1048_ = lean_ctor_get(v_a_1045_, 0);
v_tail_1049_ = lean_ctor_get(v_a_1045_, 1);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_a_1045_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1051_ = v_a_1045_;
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_tail_1049_);
lean_inc(v_head_1048_);
lean_dec(v_a_1045_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_head_1048_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v_a_1046_);
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_a_1046_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
v_a_1045_ = v_tail_1049_;
v_a_1046_ = v___x_1055_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_ks_1063_; lean_object* v_vs_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1088_; 
v_ks_1063_ = lean_ctor_get(v_x_1059_, 0);
v_vs_1064_ = lean_ctor_get(v_x_1059_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_x_1059_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1066_ = v_x_1059_;
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_vs_1064_);
lean_inc(v_ks_1063_);
lean_dec(v_x_1059_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1088_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1068_ = lean_array_get_size(v_ks_1063_);
v___x_1069_ = lean_nat_dec_lt(v_x_1060_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_dec(v_x_1060_);
v___x_1070_ = lean_array_push(v_ks_1063_, v_x_1061_);
v___x_1071_ = lean_array_push(v_vs_1064_, v_x_1062_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1071_);
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1073_ = v___x_1066_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
else
{
lean_object* v_k_x27_1075_; uint8_t v___x_1076_; 
v_k_x27_1075_ = lean_array_fget_borrowed(v_ks_1063_, v_x_1060_);
v___x_1076_ = l_Lean_instBEqMVarId_beq(v_x_1061_, v_k_x27_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1078_; 
if (v_isShared_1067_ == 0)
{
v___x_1078_ = v___x_1066_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_ks_1063_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_vs_1064_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_x_1060_, v___x_1079_);
lean_dec(v_x_1060_);
v_x_1059_ = v___x_1078_;
v_x_1060_ = v___x_1080_;
goto _start;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1083_ = lean_array_fset(v_ks_1063_, v_x_1060_, v_x_1061_);
v___x_1084_ = lean_array_fset(v_vs_1064_, v_x_1060_, v_x_1062_);
lean_dec(v_x_1060_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v___x_1084_);
lean_ctor_set(v___x_1066_, 0, v___x_1083_);
v___x_1086_ = v___x_1066_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_n_1089_, lean_object* v_k_1090_, lean_object* v_v_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_n_1089_, v___x_1092_, v_k_1090_, v_v_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1095_, size_t v_x_1096_, size_t v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
if (lean_obj_tag(v_x_1095_) == 0)
{
lean_object* v_es_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v_j_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_es_1100_ = lean_ctor_get(v_x_1095_, 0);
v___x_1101_ = ((size_t)31ULL);
v___x_1102_ = lean_usize_land(v_x_1096_, v___x_1101_);
v_j_1103_ = lean_usize_to_nat(v___x_1102_);
v___x_1104_ = lean_array_get_size(v_es_1100_);
v___x_1105_ = lean_nat_dec_lt(v_j_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec(v_j_1103_);
lean_dec(v_x_1099_);
lean_dec(v_x_1098_);
return v_x_1095_;
}
else
{
lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1144_; 
lean_inc_ref(v_es_1100_);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_x_1095_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_x_1095_, 0);
lean_dec(v_unused_1145_);
v___x_1107_ = v_x_1095_;
v_isShared_1108_ = v_isSharedCheck_1144_;
goto v_resetjp_1106_;
}
else
{
lean_dec(v_x_1095_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1144_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_v_1109_; lean_object* v___x_1110_; lean_object* v_xs_x27_1111_; lean_object* v___y_1113_; 
v_v_1109_ = lean_array_fget(v_es_1100_, v_j_1103_);
v___x_1110_ = lean_box(0);
v_xs_x27_1111_ = lean_array_fset(v_es_1100_, v_j_1103_, v___x_1110_);
switch(lean_obj_tag(v_v_1109_))
{
case 0:
{
lean_object* v_key_1118_; lean_object* v_val_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1129_; 
v_key_1118_ = lean_ctor_get(v_v_1109_, 0);
v_val_1119_ = lean_ctor_get(v_v_1109_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_v_1109_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1121_ = v_v_1109_;
v_isShared_1122_ = v_isSharedCheck_1129_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_val_1119_);
lean_inc(v_key_1118_);
lean_dec(v_v_1109_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1129_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
uint8_t v___x_1123_; 
v___x_1123_ = l_Lean_instBEqMVarId_beq(v_x_1098_, v_key_1118_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_del_object(v___x_1121_);
v___x_1124_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1118_, v_val_1119_, v_x_1098_, v_x_1099_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
v___y_1113_ = v___x_1125_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1127_; 
lean_dec(v_val_1119_);
lean_dec(v_key_1118_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_x_1099_);
lean_ctor_set(v___x_1121_, 0, v_x_1098_);
v___x_1127_ = v___x_1121_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_x_1098_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_x_1099_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v___y_1113_ = v___x_1127_;
goto v___jp_1112_;
}
}
}
}
case 1:
{
lean_object* v_node_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1142_; 
v_node_1130_ = lean_ctor_get(v_v_1109_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_v_1109_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1132_ = v_v_1109_;
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_node_1130_);
lean_dec(v_v_1109_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1142_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1134_ = ((size_t)5ULL);
v___x_1135_ = lean_usize_shift_right(v_x_1096_, v___x_1134_);
v___x_1136_ = ((size_t)1ULL);
v___x_1137_ = lean_usize_add(v_x_1097_, v___x_1136_);
v___x_1138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_node_1130_, v___x_1135_, v___x_1137_, v_x_1098_, v_x_1099_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1138_);
v___x_1140_ = v___x_1132_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
v___y_1113_ = v___x_1140_;
goto v___jp_1112_;
}
}
}
default: 
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_x_1098_);
lean_ctor_set(v___x_1143_, 1, v_x_1099_);
v___y_1113_ = v___x_1143_;
goto v___jp_1112_;
}
}
v___jp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_array_fset(v_xs_x27_1111_, v_j_1103_, v___y_1113_);
lean_dec(v_j_1103_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1114_);
v___x_1116_ = v___x_1107_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v_ks_1146_; lean_object* v_vs_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1165_; 
v_ks_1146_ = lean_ctor_get(v_x_1095_, 0);
v_vs_1147_ = lean_ctor_get(v_x_1095_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1095_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1149_ = v_x_1095_;
v_isShared_1150_ = v_isSharedCheck_1165_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_vs_1147_);
lean_inc(v_ks_1146_);
lean_dec(v_x_1095_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1165_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_ks_1146_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_vs_1147_);
v___x_1152_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v_newNode_1153_; size_t v___x_1154_; uint8_t v___x_1155_; 
v_newNode_1153_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v___x_1152_, v_x_1098_, v_x_1099_);
v___x_1154_ = ((size_t)7ULL);
v___x_1155_ = lean_usize_dec_le(v___x_1154_, v_x_1097_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1156_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1153_);
v___x_1157_ = lean_unsigned_to_nat(4u);
v___x_1158_ = lean_nat_dec_lt(v___x_1156_, v___x_1157_);
lean_dec(v___x_1156_);
if (v___x_1158_ == 0)
{
lean_object* v_ks_1159_; lean_object* v_vs_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v_ks_1159_ = lean_ctor_get(v_newNode_1153_, 0);
lean_inc_ref(v_ks_1159_);
v_vs_1160_ = lean_ctor_get(v_newNode_1153_, 1);
lean_inc_ref(v_vs_1160_);
lean_dec_ref(v_newNode_1153_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_x_1097_, v_ks_1159_, v_vs_1160_, v___x_1161_, v___x_1162_);
lean_dec_ref(v_vs_1160_);
lean_dec_ref(v_ks_1159_);
return v___x_1163_;
}
else
{
return v_newNode_1153_;
}
}
else
{
return v_newNode_1153_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(size_t v_depth_1166_, lean_object* v_keys_1167_, lean_object* v_vals_1168_, lean_object* v_i_1169_, lean_object* v_entries_1170_){
_start:
{
lean_object* v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = lean_array_get_size(v_keys_1167_);
v___x_1172_ = lean_nat_dec_lt(v_i_1169_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_dec(v_i_1169_);
return v_entries_1170_;
}
else
{
lean_object* v_k_1173_; lean_object* v_v_1174_; uint64_t v___x_1175_; size_t v_h_1176_; size_t v___x_1177_; lean_object* v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v_h_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_k_1173_ = lean_array_fget_borrowed(v_keys_1167_, v_i_1169_);
v_v_1174_ = lean_array_fget_borrowed(v_vals_1168_, v_i_1169_);
v___x_1175_ = l_Lean_instHashableMVarId_hash(v_k_1173_);
v_h_1176_ = lean_uint64_to_usize(v___x_1175_);
v___x_1177_ = ((size_t)5ULL);
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_sub(v_depth_1166_, v___x_1179_);
v___x_1181_ = lean_usize_mul(v___x_1177_, v___x_1180_);
v_h_1182_ = lean_usize_shift_right(v_h_1176_, v___x_1181_);
v___x_1183_ = lean_nat_add(v_i_1169_, v___x_1178_);
lean_dec(v_i_1169_);
lean_inc(v_v_1174_);
lean_inc(v_k_1173_);
v___x_1184_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_entries_1170_, v_h_1182_, v_depth_1166_, v_k_1173_, v_v_1174_);
v_i_1169_ = v___x_1183_;
v_entries_1170_ = v___x_1184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1186_, lean_object* v_keys_1187_, lean_object* v_vals_1188_, lean_object* v_i_1189_, lean_object* v_entries_1190_){
_start:
{
size_t v_depth_boxed_1191_; lean_object* v_res_1192_; 
v_depth_boxed_1191_ = lean_unbox_usize(v_depth_1186_);
lean_dec(v_depth_1186_);
v_res_1192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_boxed_1191_, v_keys_1187_, v_vals_1188_, v_i_1189_, v_entries_1190_);
lean_dec_ref(v_vals_1188_);
lean_dec_ref(v_keys_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
size_t v_x_2719__boxed_1198_; size_t v_x_2720__boxed_1199_; lean_object* v_res_1200_; 
v_x_2719__boxed_1198_ = lean_unbox_usize(v_x_1194_);
lean_dec(v_x_1194_);
v_x_2720__boxed_1199_ = lean_unbox_usize(v_x_1195_);
lean_dec(v_x_1195_);
v_res_1200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1193_, v_x_2719__boxed_1198_, v_x_2720__boxed_1199_, v_x_1196_, v_x_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(lean_object* v_x_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_){
_start:
{
uint64_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1204_ = l_Lean_instHashableMVarId_hash(v_x_1202_);
v___x_1205_ = lean_uint64_to_usize(v___x_1204_);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1201_, v___x_1205_, v___x_1206_, v_x_1202_, v_x_1203_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(lean_object* v_mvarId_1208_, lean_object* v_val_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v_mctx_1213_; lean_object* v_cache_1214_; lean_object* v_zetaDeltaFVarIds_1215_; lean_object* v_postponed_1216_; lean_object* v_diag_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1246_; 
v___x_1212_ = lean_st_ref_take(v___y_1210_);
v_mctx_1213_ = lean_ctor_get(v___x_1212_, 0);
v_cache_1214_ = lean_ctor_get(v___x_1212_, 1);
v_zetaDeltaFVarIds_1215_ = lean_ctor_get(v___x_1212_, 2);
v_postponed_1216_ = lean_ctor_get(v___x_1212_, 3);
v_diag_1217_ = lean_ctor_get(v___x_1212_, 4);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1219_ = v___x_1212_;
v_isShared_1220_ = v_isSharedCheck_1246_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_diag_1217_);
lean_inc(v_postponed_1216_);
lean_inc(v_zetaDeltaFVarIds_1215_);
lean_inc(v_cache_1214_);
lean_inc(v_mctx_1213_);
lean_dec(v___x_1212_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1246_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_depth_1221_; lean_object* v_levelAssignDepth_1222_; lean_object* v_lmvarCounter_1223_; lean_object* v_mvarCounter_1224_; lean_object* v_lDecls_1225_; lean_object* v_decls_1226_; lean_object* v_userNames_1227_; lean_object* v_lAssignment_1228_; lean_object* v_eAssignment_1229_; lean_object* v_dAssignment_1230_; lean_object* v_instanceTypedMVars_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1245_; 
v_depth_1221_ = lean_ctor_get(v_mctx_1213_, 0);
v_levelAssignDepth_1222_ = lean_ctor_get(v_mctx_1213_, 1);
v_lmvarCounter_1223_ = lean_ctor_get(v_mctx_1213_, 2);
v_mvarCounter_1224_ = lean_ctor_get(v_mctx_1213_, 3);
v_lDecls_1225_ = lean_ctor_get(v_mctx_1213_, 4);
v_decls_1226_ = lean_ctor_get(v_mctx_1213_, 5);
v_userNames_1227_ = lean_ctor_get(v_mctx_1213_, 6);
v_lAssignment_1228_ = lean_ctor_get(v_mctx_1213_, 7);
v_eAssignment_1229_ = lean_ctor_get(v_mctx_1213_, 8);
v_dAssignment_1230_ = lean_ctor_get(v_mctx_1213_, 9);
v_instanceTypedMVars_1231_ = lean_ctor_get(v_mctx_1213_, 10);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_mctx_1213_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1233_ = v_mctx_1213_;
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_instanceTypedMVars_1231_);
lean_inc(v_dAssignment_1230_);
lean_inc(v_eAssignment_1229_);
lean_inc(v_lAssignment_1228_);
lean_inc(v_userNames_1227_);
lean_inc(v_decls_1226_);
lean_inc(v_lDecls_1225_);
lean_inc(v_mvarCounter_1224_);
lean_inc(v_lmvarCounter_1223_);
lean_inc(v_levelAssignDepth_1222_);
lean_inc(v_depth_1221_);
lean_dec(v_mctx_1213_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_1229_, v_mvarId_1208_, v_val_1209_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 8, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_depth_1221_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_levelAssignDepth_1222_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_lmvarCounter_1223_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_mvarCounter_1224_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_lDecls_1225_);
lean_ctor_set(v_reuseFailAlloc_1244_, 5, v_decls_1226_);
lean_ctor_set(v_reuseFailAlloc_1244_, 6, v_userNames_1227_);
lean_ctor_set(v_reuseFailAlloc_1244_, 7, v_lAssignment_1228_);
lean_ctor_set(v_reuseFailAlloc_1244_, 8, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1244_, 9, v_dAssignment_1230_);
lean_ctor_set(v_reuseFailAlloc_1244_, 10, v_instanceTypedMVars_1231_);
v___x_1237_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1237_);
v___x_1239_ = v___x_1219_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_cache_1214_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_zetaDeltaFVarIds_1215_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_postponed_1216_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_diag_1217_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_st_ref_put(v___y_1210_, v___x_1239_);
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg___boxed(lean_object* v_mvarId_1247_, lean_object* v_val_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1247_, v_val_1248_, v___y_1249_);
lean_dec(v___y_1249_);
return v_res_1251_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0));
v___x_1254_ = l_Lean_stringToMessageData(v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1255_; lean_object* v_dummy_1256_; 
v___x_1255_ = lean_box(0);
v_dummy_1256_ = l_Lean_Expr_sort___override(v___x_1255_);
return v_dummy_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0(lean_object* v_mvarId_1258_, uint8_t v_addImplicitArgs_1259_, uint8_t v_nameSubgoals_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
lean_inc(v_mvarId_1258_);
v___x_1266_ = l_Lean_MVarId_getTag(v_mvarId_1258_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
lean_inc(v_mvarId_1258_);
v___x_1268_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1258_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1358_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v_fst_1270_ = lean_ctor_get(v_a_1269_, 0);
v_snd_1271_ = lean_ctor_get(v_a_1269_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_a_1269_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1273_ = v_a_1269_;
v_isShared_1274_ = v_isSharedCheck_1358_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_inc(v_fst_1270_);
lean_dec(v_a_1269_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1358_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v_a_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1270_, v___y_1262_);
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_a_1276_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_Expr_cleanupAnnotations(v_a_1276_);
v___x_1278_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v___x_1277_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; uint8_t v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_unbox(v_a_1279_);
lean_dec(v_a_1279_);
if (v___x_1280_ == 0)
{
uint8_t v___x_1281_; 
v___x_1281_ = l_Lean_Expr_isApp(v___x_1277_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
lean_dec(v_snd_1271_);
lean_dec(v_a_1267_);
lean_dec(v_mvarId_1258_);
v___x_1282_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1);
v___x_1283_ = l_Lean_indentExpr(v___x_1277_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set_tag(v___x_1273_, 7);
lean_ctor_set(v___x_1273_, 1, v___x_1283_);
lean_ctor_set(v___x_1273_, 0, v___x_1282_);
v___x_1285_ = v___x_1273_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1285_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v___x_1286_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v_dummy_1289_; lean_object* v_nargs_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_del_object(v___x_1273_);
v___x_1288_ = l_Lean_Expr_getAppFn(v___x_1277_);
v_dummy_1289_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1290_ = l_Lean_Expr_getAppNumArgs(v___x_1277_);
lean_inc(v_nargs_1290_);
v___x_1291_ = lean_mk_array(v_nargs_1290_, v_dummy_1289_);
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_nat_sub(v_nargs_1290_, v___x_1292_);
lean_dec(v_nargs_1290_);
v___x_1294_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1277_, v___x_1291_, v___x_1293_);
v___x_1295_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_a_1267_, v___x_1288_, v___x_1294_, v_addImplicitArgs_1259_, v_nameSubgoals_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v_snd_1297_; lean_object* v_fst_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v_snd_1297_ = lean_ctor_get(v_a_1296_, 1);
lean_inc(v_snd_1297_);
v_fst_1298_ = lean_ctor_get(v_a_1296_, 0);
lean_inc_n(v_fst_1298_, 2);
lean_dec(v_a_1296_);
v_fst_1299_ = lean_ctor_get(v_snd_1297_, 0);
lean_inc(v_fst_1299_);
v_snd_1300_ = lean_ctor_get(v_snd_1297_, 1);
lean_inc(v_snd_1300_);
lean_dec(v_snd_1297_);
v___x_1301_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3));
v___x_1302_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v___x_1301_, v_snd_1271_, v_fst_1298_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref_known(v___x_1302_, 1);
v___x_1303_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1258_, v_fst_1298_, v___y_1262_);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1303_, 0);
lean_dec(v_unused_1314_);
v___x_1305_ = v___x_1303_;
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v___x_1303_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1307_ = lean_array_to_list(v_fst_1299_);
v___x_1308_ = lean_array_to_list(v_snd_1300_);
v___x_1309_ = l_List_appendTR___redArg(v___x_1307_, v___x_1308_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1309_);
v___x_1311_ = v___x_1305_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec(v_snd_1300_);
lean_dec(v_fst_1299_);
lean_dec(v_fst_1298_);
lean_dec(v_mvarId_1258_);
v_a_1315_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1302_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1302_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_snd_1271_);
lean_dec(v_mvarId_1258_);
v_a_1323_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1295_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1295_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
else
{
lean_object* v___x_1331_; 
lean_dec_ref(v___x_1277_);
lean_del_object(v___x_1273_);
lean_dec(v_snd_1271_);
lean_dec(v_a_1267_);
v___x_1331_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_1258_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1341_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(v_a_1332_, v___x_1336_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1337_);
v___x_1339_ = v___x_1334_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v_a_1342_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1331_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1331_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v___x_1277_);
lean_del_object(v___x_1273_);
lean_dec(v_snd_1271_);
lean_dec(v_a_1267_);
lean_dec(v_mvarId_1258_);
v_a_1350_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1278_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1278_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_a_1267_);
lean_dec(v_mvarId_1258_);
v_a_1359_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1268_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1268_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_mvarId_1258_);
v_a_1367_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1266_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1266_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed(lean_object* v_mvarId_1375_, lean_object* v_addImplicitArgs_1376_, lean_object* v_nameSubgoals_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1383_; uint8_t v_nameSubgoals_boxed_1384_; lean_object* v_res_1385_; 
v_addImplicitArgs_boxed_1383_ = lean_unbox(v_addImplicitArgs_1376_);
v_nameSubgoals_boxed_1384_ = lean_unbox(v_nameSubgoals_1377_);
v_res_1385_ = l_Lean_Elab_Tactic_Conv_congr___lam__0(v_mvarId_1375_, v_addImplicitArgs_boxed_1383_, v_nameSubgoals_boxed_1384_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr(lean_object* v_mvarId_1386_, uint8_t v_addImplicitArgs_1387_, uint8_t v_nameSubgoals_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; 
v___x_1394_ = lean_box(v_addImplicitArgs_1387_);
v___x_1395_ = lean_box(v_nameSubgoals_1388_);
lean_inc(v_mvarId_1386_);
v___f_1396_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1396_, 0, v_mvarId_1386_);
lean_closure_set(v___f_1396_, 1, v___x_1394_);
lean_closure_set(v___f_1396_, 2, v___x_1395_);
v___x_1397_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1386_, v___f_1396_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___boxed(lean_object* v_mvarId_1398_, lean_object* v_addImplicitArgs_1399_, lean_object* v_nameSubgoals_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1406_; uint8_t v_nameSubgoals_boxed_1407_; lean_object* v_res_1408_; 
v_addImplicitArgs_boxed_1406_ = lean_unbox(v_addImplicitArgs_1399_);
v_nameSubgoals_boxed_1407_ = lean_unbox(v_nameSubgoals_1400_);
v_res_1408_ = l_Lean_Elab_Tactic_Conv_congr(v_mvarId_1398_, v_addImplicitArgs_boxed_1406_, v_nameSubgoals_boxed_1407_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(lean_object* v_mvarId_1409_, lean_object* v_val_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1409_, v_val_1410_, v___y_1412_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___boxed(lean_object* v_mvarId_1417_, lean_object* v_val_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(v_mvarId_1417_, v_val_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1(lean_object* v_00_u03b2_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_x_1426_, v_x_1427_, v_x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, size_t v_x_1432_, size_t v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1431_, v_x_1432_, v_x_1433_, v_x_1434_, v_x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
size_t v_x_3213__boxed_1443_; size_t v_x_3214__boxed_1444_; lean_object* v_res_1445_; 
v_x_3213__boxed_1443_ = lean_unbox_usize(v_x_1439_);
lean_dec(v_x_1439_);
v_x_3214__boxed_1444_ = lean_unbox_usize(v_x_1440_);
lean_dec(v_x_1440_);
v_res_1445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(v_00_u03b2_1437_, v_x_1438_, v_x_3213__boxed_1443_, v_x_3214__boxed_1444_, v_x_1441_, v_x_1442_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1446_, lean_object* v_n_1447_, lean_object* v_k_1448_, lean_object* v_v_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v_n_1447_, v_k_1448_, v_v_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1451_, size_t v_depth_1452_, lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_heq_1455_, lean_object* v_i_1456_, lean_object* v_entries_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_1452_, v_keys_1453_, v_vals_1454_, v_i_1456_, v_entries_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_depth_1460_, lean_object* v_keys_1461_, lean_object* v_vals_1462_, lean_object* v_heq_1463_, lean_object* v_i_1464_, lean_object* v_entries_1465_){
_start:
{
size_t v_depth_boxed_1466_; lean_object* v_res_1467_; 
v_depth_boxed_1466_ = lean_unbox_usize(v_depth_1460_);
lean_dec(v_depth_1460_);
v_res_1467_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(v_00_u03b2_1459_, v_depth_boxed_1466_, v_keys_1461_, v_vals_1462_, v_heq_1463_, v_i_1464_, v_entries_1465_);
lean_dec_ref(v_vals_1462_);
lean_dec_ref(v_keys_1461_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_x_1469_, v_x_1470_, v_x_1471_, v_x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
if (lean_obj_tag(v_a_1474_) == 0)
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_array_to_list(v_a_1475_);
return v___x_1476_;
}
else
{
lean_object* v_head_1477_; 
v_head_1477_ = lean_ctor_get(v_a_1474_, 0);
if (lean_obj_tag(v_head_1477_) == 0)
{
lean_object* v_tail_1478_; 
v_tail_1478_ = lean_ctor_get(v_a_1474_, 1);
lean_inc(v_tail_1478_);
lean_dec_ref_known(v_a_1474_, 2);
v_a_1474_ = v_tail_1478_;
goto _start;
}
else
{
lean_object* v_tail_1480_; lean_object* v_val_1481_; lean_object* v___x_1482_; 
lean_inc_ref(v_head_1477_);
v_tail_1480_ = lean_ctor_get(v_a_1474_, 1);
lean_inc(v_tail_1480_);
lean_dec_ref_known(v_a_1474_, 2);
v_val_1481_ = lean_ctor_get(v_head_1477_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v_head_1477_, 1);
v___x_1482_ = lean_array_push(v_a_1475_, v_val_1481_);
v_a_1474_ = v_tail_1480_;
v_a_1475_ = v___x_1482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg(lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; uint8_t v___x_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1494_ = 0;
v___x_1495_ = 1;
v___x_1496_ = l_Lean_Elab_Tactic_Conv_congr(v_a_1493_, v___x_1494_, v___x_1495_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0));
v___x_1499_ = l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(v_a_1497_, v___x_1498_);
v___x_1500_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1499_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
return v___x_1500_;
}
else
{
lean_object* v_a_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1508_; 
v_a_1501_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1503_ = v___x_1496_;
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_a_1501_);
lean_dec(v___x_1496_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1508_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1506_; 
if (v_isShared_1504_ == 0)
{
v___x_1506_ = v___x_1503_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1492_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1492_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___boxed(lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
lean_dec(v_a_1521_);
lean_dec_ref(v_a_1520_);
lean_dec(v_a_1519_);
lean_dec_ref(v_a_1518_);
lean_dec(v_a_1517_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr(lean_object* v_x_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1526_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___boxed(lean_object* v_x_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Elab_Tactic_Conv_evalCongr(v_x_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_x_1535_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1(){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1560_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0));
v___x_1562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1563_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCongr___boxed), 10, 0);
v___x_1564_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1560_, v___x_1561_, v___x_1562_, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___boxed(lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3(){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6));
v___x_1595_ = l_Lean_addBuiltinDeclarationRanges(v___x_1593_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___boxed(lean_object* v_a_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(lean_object* v_as_1598_, size_t v_i_1599_, size_t v_stop_1600_, lean_object* v_b_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_usize_dec_eq(v_i_1599_, v_stop_1600_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_array_uget_borrowed(v_as_1598_, v_i_1599_);
lean_inc(v___x_1608_);
v___x_1609_ = l_Lean_Meta_mkCongrFun(v_b_1601_, v___x_1608_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; size_t v___x_1611_; size_t v___x_1612_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1609_, 1);
v___x_1611_ = ((size_t)1ULL);
v___x_1612_ = lean_usize_add(v_i_1599_, v___x_1611_);
v_i_1599_ = v___x_1612_;
v_b_1601_ = v_a_1610_;
goto _start;
}
else
{
return v___x_1609_;
}
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v_b_1601_);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0___boxed(lean_object* v_as_1615_, lean_object* v_i_1616_, lean_object* v_stop_1617_, lean_object* v_b_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
size_t v_i_boxed_1624_; size_t v_stop_boxed_1625_; lean_object* v_res_1626_; 
v_i_boxed_1624_ = lean_unbox_usize(v_i_1616_);
lean_dec(v_i_1616_);
v_stop_boxed_1625_ = lean_unbox_usize(v_stop_1617_);
lean_dec(v_stop_1617_);
v_res_1626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_as_1615_, v_i_boxed_1624_, v_stop_boxed_1625_, v_b_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_as_1615_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(lean_object* v_mvarId_1628_, lean_object* v_snd_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
if (lean_obj_tag(v_x_1630_) == 5)
{
lean_object* v_fn_1638_; lean_object* v_arg_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_fn_1638_ = lean_ctor_get(v_x_1630_, 0);
lean_inc_ref(v_fn_1638_);
v_arg_1639_ = lean_ctor_get(v_x_1630_, 1);
lean_inc_ref(v_arg_1639_);
lean_dec_ref_known(v_x_1630_, 2);
v___x_1640_ = lean_array_set(v_x_1631_, v_x_1632_, v_arg_1639_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v___x_1642_ = lean_nat_sub(v_x_1632_, v___x_1641_);
lean_dec(v_x_1632_);
v_x_1630_ = v_fn_1638_;
v_x_1631_ = v___x_1640_;
v_x_1632_ = v___x_1642_;
goto _start;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_dec(v_x_1632_);
v___x_1644_ = lean_box(0);
v___x_1645_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_x_1630_, v___x_1644_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v_fst_1647_; lean_object* v_snd_1648_; lean_object* v_a_1650_; lean_object* v___y_1673_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v_fst_1647_ = lean_ctor_get(v_a_1646_, 0);
lean_inc(v_fst_1647_);
v_snd_1648_ = lean_ctor_get(v_a_1646_, 1);
lean_inc(v_snd_1648_);
lean_dec(v_a_1646_);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_array_get_size(v_x_1631_);
v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_inc(v_snd_1648_);
v_a_1650_ = v_snd_1648_;
goto v___jp_1649_;
}
else
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_nat_dec_le(v___x_1684_, v___x_1684_);
if (v___x_1686_ == 0)
{
if (v___x_1685_ == 0)
{
lean_inc(v_snd_1648_);
v_a_1650_ = v_snd_1648_;
goto v___jp_1649_;
}
else
{
size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = lean_usize_of_nat(v___x_1684_);
lean_inc(v_snd_1648_);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1631_, v___x_1687_, v___x_1688_, v_snd_1648_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
v___y_1673_ = v___x_1689_;
goto v___jp_1672_;
}
}
else
{
size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = lean_usize_of_nat(v___x_1684_);
lean_inc(v_snd_1648_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1631_, v___x_1690_, v___x_1691_, v_snd_1648_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
v___y_1673_ = v___x_1692_;
goto v___jp_1672_;
}
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1651_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1628_, v_a_1650_, v___y_1634_);
lean_dec_ref(v___x_1651_);
v___x_1652_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0));
v___x_1653_ = l_Lean_mkAppN(v_fst_1647_, v_x_1631_);
lean_dec_ref(v_x_1631_);
v___x_1654_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_1652_, v_snd_1629_, v___x_1653_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1662_; 
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1654_, 0);
lean_dec(v_unused_1663_);
v___x_1656_ = v___x_1654_;
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v___x_1654_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1662_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = l_Lean_Expr_mvarId_x21(v_snd_1648_);
lean_dec(v_snd_1648_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v___x_1658_);
v___x_1660_ = v___x_1656_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_snd_1648_);
v_a_1664_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1654_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1654_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
v___jp_1672_:
{
if (lean_obj_tag(v___y_1673_) == 0)
{
lean_object* v_a_1674_; 
v_a_1674_ = lean_ctor_get(v___y_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___y_1673_, 1);
v_a_1650_ = v_a_1674_;
goto v___jp_1649_;
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
lean_dec(v_snd_1648_);
lean_dec(v_fst_1647_);
lean_dec_ref(v_x_1631_);
lean_dec_ref(v_snd_1629_);
lean_dec(v_mvarId_1628_);
v_a_1675_ = lean_ctor_get(v___y_1673_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___y_1673_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___y_1673_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___y_1673_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v_x_1631_);
lean_dec_ref(v_snd_1629_);
lean_dec(v_mvarId_1628_);
v_a_1693_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1645_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1645_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___boxed(lean_object* v_mvarId_1701_, lean_object* v_snd_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1701_, v_snd_1702_, v_x_1703_, v_x_1704_, v_x_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1711_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0));
v___x_1714_ = l_Lean_stringToMessageData(v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(lean_object* v_mvarId_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
lean_inc(v_mvarId_1715_);
v___x_1721_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1757_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v_fst_1723_ = lean_ctor_get(v_a_1722_, 0);
v_snd_1724_ = lean_ctor_get(v_a_1722_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_a_1722_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1726_ = v_a_1722_;
v_isShared_1727_ = v_isSharedCheck_1757_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
lean_dec(v_a_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1757_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v_a_1729_; lean_object* v___x_1730_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; uint8_t v___x_1742_; 
v___x_1728_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1723_, v___y_1717_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = l_Lean_Expr_cleanupAnnotations(v_a_1729_);
v___x_1742_ = l_Lean_Expr_isApp(v___x_1730_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
lean_dec(v_snd_1724_);
lean_dec(v_mvarId_1715_);
v___x_1743_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1);
v___x_1744_ = l_Lean_indentExpr(v___x_1730_);
if (v_isShared_1727_ == 0)
{
lean_ctor_set_tag(v___x_1726_, 7);
lean_ctor_set(v___x_1726_, 1, v___x_1744_);
lean_ctor_set(v___x_1726_, 0, v___x_1743_);
v___x_1746_ = v___x_1726_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v___x_1747_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1746_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1747_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1747_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_del_object(v___x_1726_);
v___y_1732_ = v___y_1716_;
v___y_1733_ = v___y_1717_;
v___y_1734_ = v___y_1718_;
v___y_1735_ = v___y_1719_;
goto v___jp_1731_;
}
v___jp_1731_:
{
lean_object* v_dummy_1736_; lean_object* v_nargs_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_dummy_1736_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1737_ = l_Lean_Expr_getAppNumArgs(v___x_1730_);
lean_inc(v_nargs_1737_);
v___x_1738_ = lean_mk_array(v_nargs_1737_, v_dummy_1736_);
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_nat_sub(v_nargs_1737_, v___x_1739_);
lean_dec(v_nargs_1737_);
v___x_1741_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1715_, v_snd_1724_, v___x_1730_, v___x_1738_, v___x_1740_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1741_;
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_mvarId_1715_);
v_a_1758_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1721_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1721_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed(lean_object* v_mvarId_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(v_mvarId_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN(lean_object* v_mvarId_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___f_1779_; lean_object* v___x_1780_; 
lean_inc(v_mvarId_1773_);
v___f_1779_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1779_, 0, v_mvarId_1773_);
v___x_1780_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1773_, v___f_1779_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___boxed(lean_object* v_mvarId_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_mvarId_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(lean_object* v_msg_1788_){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = lean_box(0);
v___x_1790_ = lean_panic_fn_borrowed(v___x_1789_, v_msg_1788_);
return v___x_1790_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1792_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_1793_ = lean_unsigned_to_nat(30u);
v___x_1794_ = lean_unsigned_to_nat(150u);
v___x_1795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__0));
v___x_1796_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_1797_ = l_mkPanicMessageWithDecl(v___x_1796_, v___x_1795_, v___x_1794_, v___x_1793_, v___x_1792_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(lean_object* v_fst_1798_, lean_object* v_snd_1799_, lean_object* v_fst_1800_, lean_object* v_fst_1801_, lean_object* v_00___1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1);
v___x_1809_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_1808_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1820_; 
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1821_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1820_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1820_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_fst_1798_);
lean_ctor_set(v___x_1813_, 1, v_snd_1799_);
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_fst_1800_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_fst_1801_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1816_);
v___x_1818_ = v___x_1811_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_fst_1801_);
lean_dec(v_fst_1800_);
lean_dec(v_snd_1799_);
lean_dec(v_fst_1798_);
v_a_1822_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1809_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1809_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___boxed(lean_object* v_fst_1830_, lean_object* v_snd_1831_, lean_object* v_fst_1832_, lean_object* v_fst_1833_, lean_object* v_00___1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1830_, v_snd_1831_, v_fst_1832_, v_fst_1833_, v_00___1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(lean_object* v_snd_1841_, lean_object* v_snd_1842_, lean_object* v___x_1843_, lean_object* v___x_1844_, lean_object* v_____r_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1851_ = l_Lean_Expr_mvarId_x21(v_snd_1841_);
v___x_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v_snd_1842_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1843_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1844_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1___boxed(lean_object* v_snd_1858_, lean_object* v_snd_1859_, lean_object* v___x_1860_, lean_object* v___x_1861_, lean_object* v_____r_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1858_, v_snd_1859_, v___x_1860_, v___x_1861_, v_____r_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec_ref(v_snd_1858_);
return v_res_1868_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__0));
v___x_1871_ = l_Lean_stringToMessageData(v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(lean_object* v_upperBound_1872_, lean_object* v_args_1873_, lean_object* v___x_1874_, lean_object* v_origTag_1875_, lean_object* v_tacticName_1876_, lean_object* v_a_1877_, lean_object* v_b_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_a_1885_; lean_object* v___y_1890_; uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_lt(v_a_1877_, v_upperBound_1872_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1910_; 
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v_b_1878_);
return v___x_1910_;
}
else
{
lean_object* v_snd_1911_; lean_object* v_snd_1912_; lean_object* v_fst_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_2034_; 
v_snd_1911_ = lean_ctor_get(v_b_1878_, 1);
lean_inc(v_snd_1911_);
v_snd_1912_ = lean_ctor_get(v_snd_1911_, 1);
lean_inc(v_snd_1912_);
v_fst_1913_ = lean_ctor_get(v_b_1878_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_b_1878_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_b_1878_, 1);
lean_dec(v_unused_2035_);
v___x_1915_ = v_b_1878_;
v_isShared_1916_ = v_isSharedCheck_2034_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_fst_1913_);
lean_dec(v_b_1878_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_2034_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_fst_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_2032_; 
v_fst_1917_ = lean_ctor_get(v_snd_1911_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_snd_1911_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_snd_1911_, 1);
lean_dec(v_unused_2033_);
v___x_1919_ = v_snd_1911_;
v_isShared_1920_ = v_isSharedCheck_2032_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_fst_1917_);
lean_dec(v_snd_1911_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_2032_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_fst_1921_; lean_object* v_snd_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_2031_; 
v_fst_1921_ = lean_ctor_get(v_snd_1912_, 0);
v_snd_1922_ = lean_ctor_get(v_snd_1912_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_snd_1912_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1924_ = v_snd_1912_;
v_isShared_1925_ = v_isSharedCheck_2031_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snd_1922_);
lean_inc(v_fst_1921_);
lean_dec(v_snd_1912_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_2031_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1926_ = l_Lean_instInhabitedExpr;
v___x_1927_ = lean_array_get_borrowed(v___x_1926_, v_args_1873_, v_a_1877_);
v___x_1928_ = lean_array_fget_borrowed(v___x_1874_, v_a_1877_);
v___x_1929_ = lean_unbox(v___x_1928_);
switch(v___x_1929_)
{
case 1:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_del_object(v___x_1924_);
lean_del_object(v___x_1919_);
lean_del_object(v___x_1915_);
v___x_1930_ = lean_box(0);
v___x_1931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1921_, v_snd_1922_, v_fst_1917_, v_fst_1913_, v___x_1930_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
v___y_1890_ = v___x_1931_;
goto v___jp_1889_;
}
case 2:
{
lean_object* v___x_1932_; 
lean_del_object(v___x_1924_);
lean_del_object(v___x_1919_);
lean_del_object(v___x_1915_);
lean_inc(v_origTag_1875_);
lean_inc(v___x_1927_);
v___x_1932_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_1927_, v_origTag_1875_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v_fst_1934_; lean_object* v_snd_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1961_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v_fst_1934_ = lean_ctor_get(v_a_1933_, 0);
v_snd_1935_ = lean_ctor_get(v_a_1933_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_a_1933_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1937_ = v_a_1933_;
v_isShared_1938_ = v_isSharedCheck_1961_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_snd_1935_);
lean_inc(v_fst_1934_);
lean_dec(v_a_1933_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1961_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
lean_inc(v_fst_1934_);
v___x_1939_ = l_Lean_Expr_app___override(v_fst_1913_, v_fst_1934_);
lean_inc(v_snd_1935_);
lean_inc(v___x_1927_);
v___x_1940_ = l_Lean_mkApp3(v_fst_1917_, v___x_1927_, v_fst_1934_, v_snd_1935_);
if (lean_obj_tag(v_fst_1921_) == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_del_object(v___x_1937_);
v___x_1941_ = lean_box(0);
v___x_1942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1935_, v_snd_1922_, v___x_1940_, v___x_1939_, v___x_1941_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v_snd_1935_);
v___y_1890_ = v___x_1942_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_dec_ref_known(v_fst_1921_, 1);
v___x_1943_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
lean_inc_ref(v_tacticName_1876_);
v___x_1944_ = l_Lean_stringToMessageData(v_tacticName_1876_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set_tag(v___x_1937_, 7);
lean_ctor_set(v___x_1937_, 1, v___x_1944_);
lean_ctor_set(v___x_1937_, 0, v___x_1943_);
v___x_1946_ = v___x_1937_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1948_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1951_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1935_, v_snd_1922_, v___x_1940_, v___x_1939_, v_a_1950_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v_snd_1935_);
v___y_1890_ = v___x_1951_;
goto v___jp_1889_;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v___x_1940_);
lean_dec_ref(v___x_1939_);
lean_dec(v_snd_1935_);
lean_dec(v_snd_1922_);
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v_a_1952_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1949_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1949_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_snd_1922_);
lean_dec(v_fst_1921_);
lean_dec(v_fst_1917_);
lean_dec(v_fst_1913_);
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v_a_1962_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1932_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1932_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
case 4:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_del_object(v___x_1924_);
lean_del_object(v___x_1919_);
lean_del_object(v___x_1915_);
v___x_1970_ = lean_box(0);
v___x_1971_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1921_, v_snd_1922_, v_fst_1917_, v_fst_1913_, v___x_1970_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
v___y_1890_ = v___x_1971_;
goto v___jp_1889_;
}
case 5:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_inc(v___x_1927_);
v___x_1972_ = l_Lean_Expr_app___override(v_fst_1917_, v___x_1927_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
lean_inc_ref(v___y_1879_);
lean_inc_ref(v___x_1972_);
v___x_1973_ = lean_infer_type(v___x_1972_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
lean_inc_ref(v___y_1879_);
v___x_1975_ = lean_whnf(v_a_1974_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
v___x_1977_ = l_Lean_Expr_bindingDomain_x21(v_a_1976_);
lean_dec(v_a_1976_);
v___x_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
v___x_1979_ = 0;
v___x_1980_ = lean_box(0);
v___x_1981_ = l_Lean_Meta_mkFreshExprMVar(v___x_1978_, v___x_1979_, v___x_1980_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc_n(v_a_1982_, 3);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = l_Lean_Expr_app___override(v_fst_1913_, v_a_1982_);
v___x_1984_ = l_Lean_Expr_app___override(v___x_1972_, v_a_1982_);
v___x_1985_ = l_Lean_Expr_mvarId_x21(v_a_1982_);
lean_dec(v_a_1982_);
v___x_1986_ = lean_array_push(v_snd_1922_, v___x_1985_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1986_);
v___x_1988_ = v___x_1924_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_fst_1921_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1988_);
lean_ctor_set(v___x_1919_, 0, v___x_1984_);
v___x_1990_ = v___x_1919_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1990_);
lean_ctor_set(v___x_1915_, 0, v___x_1983_);
v___x_1992_ = v___x_1915_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
v_a_1885_ = v___x_1992_;
goto v___jp_1884_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v___x_1972_);
lean_del_object(v___x_1924_);
lean_dec(v_snd_1922_);
lean_dec(v_fst_1921_);
lean_del_object(v___x_1919_);
lean_del_object(v___x_1915_);
lean_dec(v_fst_1913_);
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v_a_1996_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1981_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1981_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v___x_1972_);
lean_del_object(v___x_1924_);
lean_dec(v_snd_1922_);
lean_dec(v_fst_1921_);
lean_del_object(v___x_1919_);
lean_del_object(v___x_1915_);
lean_dec(v_fst_1913_);
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v_a_2004_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1975_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1975_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v___x_1972_);
lean_del_object(v___x_1924_);
lean_dec(v_snd_1922_);
lean_dec(v_fst_1921_);
lean_del_object(v___x_1919_);
lean_del_object(v___x_1915_);
lean_dec(v_fst_1913_);
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v_a_2012_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1973_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1973_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
default: 
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_inc_n(v___x_1927_, 2);
v___x_2020_ = l_Lean_Expr_app___override(v_fst_1913_, v___x_1927_);
v___x_2021_ = l_Lean_Expr_app___override(v_fst_1917_, v___x_1927_);
if (v_isShared_1925_ == 0)
{
v___x_2023_ = v___x_1924_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_fst_1921_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_snd_1922_);
v___x_2023_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_2023_);
lean_ctor_set(v___x_1919_, 0, v___x_2021_);
v___x_2025_ = v___x_1919_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_2025_);
lean_ctor_set(v___x_1915_, 0, v___x_2020_);
v___x_2027_ = v___x_1915_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
v_a_1885_ = v___x_2027_;
goto v___jp_1884_;
}
}
}
}
}
}
}
}
}
v___jp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = lean_nat_add(v_a_1877_, v___x_1886_);
lean_dec(v_a_1877_);
v_a_1877_ = v___x_1887_;
v_b_1878_ = v_a_1885_;
goto _start;
}
v___jp_1889_:
{
if (lean_obj_tag(v___y_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1900_; 
v_a_1891_ = lean_ctor_get(v___y_1890_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___y_1890_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1893_ = v___y_1890_;
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___y_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
if (lean_obj_tag(v_a_1891_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; 
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v_a_1895_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_a_1895_);
lean_dec_ref_known(v_a_1891_, 1);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v_a_1895_);
v___x_1897_ = v___x_1893_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
else
{
lean_object* v_a_1899_; 
lean_del_object(v___x_1893_);
v_a_1899_ = lean_ctor_get(v_a_1891_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v_a_1891_, 1);
v_a_1885_ = v_a_1899_;
goto v___jp_1884_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1877_);
lean_dec_ref(v_tacticName_1876_);
lean_dec(v_origTag_1875_);
v_a_1901_ = lean_ctor_get(v___y_1890_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___y_1890_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___y_1890_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___y_1890_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___boxed(lean_object* v_upperBound_2036_, lean_object* v_args_2037_, lean_object* v___x_2038_, lean_object* v_origTag_2039_, lean_object* v_tacticName_2040_, lean_object* v_a_2041_, lean_object* v_b_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2036_, v_args_2037_, v___x_2038_, v_origTag_2039_, v_tacticName_2040_, v_a_2041_, v_b_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec_ref(v___x_2038_);
lean_dec_ref(v_args_2037_);
lean_dec(v_upperBound_2036_);
return v_res_2048_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2052_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2));
v___x_2053_ = lean_unsigned_to_nat(14u);
v___x_2054_ = lean_unsigned_to_nat(22u);
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1));
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0));
v___x_2057_ = l_mkPanicMessageWithDecl(v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_, v___x_2052_);
return v___x_2057_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5));
v___x_2063_ = l_Lean_stringToMessageData(v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(lean_object* v_tacticName_2064_, lean_object* v_origTag_2065_, lean_object* v_f_2066_, lean_object* v_args_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v_lower_2088_; lean_object* v_upper_2089_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = lean_array_get_size(v_args_2067_);
lean_inc_ref(v_f_2066_);
v___x_2106_ = l_Lean_Meta_getFunInfoNArgs(v_f_2066_, v___x_2105_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_a_2107_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; uint8_t v___x_2110_; lean_object* v___x_2111_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = 0;
lean_inc_ref(v_f_2066_);
v___x_2111_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_2066_, v_a_2107_, v_a_2109_, v___x_2110_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
if (lean_obj_tag(v_a_2112_) == 1)
{
lean_object* v_val_2113_; lean_object* v_proof_2114_; lean_object* v_argKinds_2115_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_val_2113_ = lean_ctor_get(v_a_2112_, 0);
lean_inc(v_val_2113_);
lean_dec_ref_known(v_a_2112_, 1);
v_proof_2114_ = lean_ctor_get(v_val_2113_, 1);
lean_inc_ref(v_proof_2114_);
v_argKinds_2115_ = lean_ctor_get(v_val_2113_, 2);
lean_inc_ref(v_argKinds_2115_);
lean_dec(v_val_2113_);
v___x_2142_ = 0;
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_box(v___x_2142_);
v___x_2145_ = lean_array_get(v___x_2144_, v_argKinds_2115_, v___x_2143_);
lean_dec(v___x_2144_);
v___x_2146_ = lean_unbox(v___x_2145_);
lean_dec(v___x_2145_);
if (v___x_2146_ == 2)
{
v___y_2117_ = v_a_2068_;
v___y_2118_ = v_a_2069_;
v___y_2119_ = v_a_2070_;
v___y_2120_ = v_a_2071_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v_argKinds_2115_);
lean_dec_ref(v_proof_2114_);
lean_dec_ref(v_args_2067_);
lean_dec_ref(v_f_2066_);
lean_dec(v_origTag_2065_);
v___x_2147_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2148_ = l_Lean_stringToMessageData(v_tacticName_2064_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2151_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
v___jp_2116_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2121_ = lean_array_get_size(v_argKinds_2115_);
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4));
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v_proof_2114_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_f_2066_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v___x_2121_, v_args_2067_, v_argKinds_2115_, v_origTag_2065_, v_tacticName_2064_, v___x_2122_, v___x_2125_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec_ref(v_argKinds_2115_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v_snd_2128_; lean_object* v_snd_2129_; lean_object* v_fst_2130_; lean_object* v_fst_2131_; lean_object* v_snd_2132_; uint8_t v___x_2133_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_snd_2128_ = lean_ctor_get(v_a_2127_, 1);
lean_inc(v_snd_2128_);
lean_dec(v_a_2127_);
v_snd_2129_ = lean_ctor_get(v_snd_2128_, 1);
lean_inc(v_snd_2129_);
v_fst_2130_ = lean_ctor_get(v_snd_2128_, 0);
lean_inc(v_fst_2130_);
lean_dec(v_snd_2128_);
v_fst_2131_ = lean_ctor_get(v_snd_2129_, 0);
lean_inc(v_fst_2131_);
v_snd_2132_ = lean_ctor_get(v_snd_2129_, 1);
lean_inc(v_snd_2132_);
lean_dec(v_snd_2129_);
v___x_2133_ = lean_nat_dec_le(v___x_2121_, v___x_2122_);
if (v___x_2133_ == 0)
{
v___y_2081_ = v_snd_2132_;
v___y_2082_ = v___y_2118_;
v___y_2083_ = v___y_2120_;
v___y_2084_ = v_fst_2130_;
v___y_2085_ = v_fst_2131_;
v___y_2086_ = v___y_2117_;
v___y_2087_ = v___y_2119_;
v_lower_2088_ = v___x_2121_;
v_upper_2089_ = v___x_2105_;
goto v___jp_2080_;
}
else
{
v___y_2081_ = v_snd_2132_;
v___y_2082_ = v___y_2118_;
v___y_2083_ = v___y_2120_;
v___y_2084_ = v_fst_2130_;
v___y_2085_ = v_fst_2131_;
v___y_2086_ = v___y_2117_;
v___y_2087_ = v___y_2119_;
v_lower_2088_ = v___x_2122_;
v_upper_2089_ = v___x_2105_;
goto v___jp_2080_;
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec_ref(v_args_2067_);
v_a_2134_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2126_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2126_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_args_2067_);
lean_dec_ref(v_f_2066_);
lean_dec(v_origTag_2065_);
v___x_2161_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2162_ = l_Lean_stringToMessageData(v_tacticName_2064_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2165_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2166_;
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v_args_2067_);
lean_dec_ref(v_f_2066_);
lean_dec(v_origTag_2065_);
lean_dec_ref(v_tacticName_2064_);
v_a_2167_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2111_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2111_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_a_2107_);
lean_dec_ref(v_args_2067_);
lean_dec_ref(v_f_2066_);
lean_dec(v_origTag_2065_);
lean_dec_ref(v_tacticName_2064_);
v_a_2175_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2108_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2108_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v_args_2067_);
lean_dec_ref(v_f_2066_);
lean_dec(v_origTag_2065_);
lean_dec_ref(v_tacticName_2064_);
v_a_2183_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2106_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2106_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
v___jp_2073_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___y_2076_);
lean_ctor_set(v___x_2077_, 1, v___y_2074_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___y_2075_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
v___jp_2080_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = l_Array_toSubarray___redArg(v_args_2067_, v_lower_2088_, v_upper_2089_);
v___x_2091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_2090_, v___y_2084_, v___y_2086_, v___y_2082_, v___y_2087_, v___y_2083_);
if (lean_obj_tag(v___x_2091_) == 0)
{
if (lean_obj_tag(v___y_2085_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3);
v___x_2094_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(v___x_2093_);
v___y_2074_ = v___y_2081_;
v___y_2075_ = v_a_2092_;
v___y_2076_ = v___x_2094_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2095_; lean_object* v_val_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2091_, 1);
v_val_2096_ = lean_ctor_get(v___y_2085_, 0);
lean_inc(v_val_2096_);
lean_dec_ref_known(v___y_2085_, 1);
v___y_2074_ = v___y_2081_;
v___y_2075_ = v_a_2095_;
v___y_2076_ = v_val_2096_;
goto v___jp_2073_;
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v___y_2085_);
lean_dec(v___y_2081_);
v_a_2097_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2091_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2091_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___boxed(lean_object* v_tacticName_2191_, lean_object* v_origTag_2192_, lean_object* v_f_2193_, lean_object* v_args_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_2191_, v_origTag_2192_, v_f_2193_, v_args_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(lean_object* v_upperBound_2201_, lean_object* v_args_2202_, lean_object* v___x_2203_, lean_object* v_origTag_2204_, lean_object* v_tacticName_2205_, lean_object* v_inst_2206_, lean_object* v_R_2207_, lean_object* v_a_2208_, lean_object* v_b_2209_, lean_object* v_c_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2201_, v_args_2202_, v___x_2203_, v_origTag_2204_, v_tacticName_2205_, v_a_2208_, v_b_2209_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___boxed(lean_object* v_upperBound_2217_, lean_object* v_args_2218_, lean_object* v___x_2219_, lean_object* v_origTag_2220_, lean_object* v_tacticName_2221_, lean_object* v_inst_2222_, lean_object* v_R_2223_, lean_object* v_a_2224_, lean_object* v_b_2225_, lean_object* v_c_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(v_upperBound_2217_, v_args_2218_, v___x_2219_, v_origTag_2220_, v_tacticName_2221_, v_inst_2222_, v_R_2223_, v_a_2224_, v_b_2225_, v_c_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec_ref(v___x_2219_);
lean_dec_ref(v_args_2218_);
lean_dec(v_upperBound_2217_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(lean_object* v_msg_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___f_2239_; lean_object* v___x_3764__overap_2240_; lean_object* v___x_2241_; 
v___f_2239_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_3764__overap_2240_ = lean_panic_fn_borrowed(v___f_2239_, v_msg_2233_);
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
v___x_2241_ = lean_apply_5(v___x_3764__overap_2240_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, lean_box(0));
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1___boxed(lean_object* v_msg_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v_msg_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(lean_object* v_binderType_2252_, lean_object* v_mvarId_2253_, lean_object* v_body_2254_, uint8_t v_domain_2255_, uint8_t v___x_2256_, lean_object* v_binderName_2257_, lean_object* v_tacticName_2258_, lean_object* v_rhs_2259_, lean_object* v_arg_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
lean_inc_ref(v_binderType_2252_);
v___x_2266_ = l_Lean_Meta_getLevel(v_binderType_2252_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
lean_inc(v_mvarId_2253_);
v___x_2268_ = l_Lean_MVarId_getTag(v_mvarId_2253_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___x_2270_ = lean_expr_instantiate1(v_body_2254_, v_arg_2260_);
lean_inc_ref(v___x_2270_);
v___x_2271_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_2270_, v_a_2269_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v_fst_2273_; lean_object* v_snd_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2348_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v_fst_2273_ = lean_ctor_get(v_a_2272_, 0);
v_snd_2274_ = lean_ctor_get(v_a_2272_, 1);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_a_2272_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2276_ = v_a_2272_;
v_isShared_2277_ = v_isSharedCheck_2348_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_snd_2274_);
lean_inc(v_fst_2273_);
lean_dec(v_a_2272_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2348_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_Meta_getLevel(v___x_2270_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_mk_empty_array_with_capacity(v___x_2280_);
v___x_2282_ = lean_array_push(v___x_2281_, v_arg_2260_);
v___x_2283_ = 1;
v___x_2284_ = l_Lean_Meta_mkLambdaFVars(v___x_2282_, v_fst_2273_, v_domain_2255_, v___x_2256_, v_domain_2255_, v___x_2256_, v___x_2283_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
lean_inc(v_snd_2274_);
v___x_2286_ = l_Lean_Meta_mkLambdaFVars(v___x_2282_, v_snd_2274_, v_domain_2255_, v___x_2256_, v_domain_2255_, v___x_2256_, v___x_2283_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec_ref(v___x_2282_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1));
v___x_2289_ = lean_box(0);
if (v_isShared_2277_ == 0)
{
lean_ctor_set_tag(v___x_2276_, 1);
lean_ctor_set(v___x_2276_, 1, v___x_2289_);
lean_ctor_set(v___x_2276_, 0, v_a_2279_);
v___x_2291_ = v___x_2276_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2279_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2292_, 0, v_a_2267_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_Expr_const___override(v___x_2288_, v___x_2292_);
v___x_2294_ = 0;
lean_inc_ref(v_binderType_2252_);
v___x_2295_ = l_Lean_Expr_lam___override(v_binderName_2257_, v_binderType_2252_, v_body_2254_, v___x_2294_);
v___x_2296_ = lean_unsigned_to_nat(4u);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___x_2296_);
v___x_2298_ = lean_array_push(v___x_2297_, v_binderType_2252_);
v___x_2299_ = lean_array_push(v___x_2298_, v___x_2295_);
v___x_2300_ = lean_array_push(v___x_2299_, v_a_2285_);
v___x_2301_ = lean_array_push(v___x_2300_, v_a_2287_);
v___x_2302_ = l_Lean_mkAppN(v___x_2293_, v___x_2301_);
lean_dec_ref(v___x_2301_);
lean_inc_ref(v___x_2302_);
v___x_2303_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2258_, v_rhs_2259_, v___x_2302_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref_known(v___x_2303_, 1);
v___x_2304_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2253_, v___x_2302_, v___y_2262_);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2313_ == 0)
{
lean_object* v_unused_2314_; 
v_unused_2314_ = lean_ctor_get(v___x_2304_, 0);
lean_dec(v_unused_2314_);
v___x_2306_ = v___x_2304_;
v_isShared_2307_ = v_isSharedCheck_2313_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v___x_2304_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2313_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2308_ = l_Lean_Expr_mvarId_x21(v_snd_2274_);
lean_dec(v_snd_2274_);
v___x_2309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v___x_2289_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2309_);
v___x_2311_ = v___x_2306_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v___x_2302_);
lean_dec(v_snd_2274_);
lean_dec(v_mvarId_2253_);
v_a_2315_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2303_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2303_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_a_2285_);
lean_dec(v_a_2279_);
lean_del_object(v___x_2276_);
lean_dec(v_snd_2274_);
lean_dec(v_a_2267_);
lean_dec_ref(v_rhs_2259_);
lean_dec_ref(v_tacticName_2258_);
lean_dec(v_binderName_2257_);
lean_dec_ref(v_body_2254_);
lean_dec(v_mvarId_2253_);
lean_dec_ref(v_binderType_2252_);
v_a_2324_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2286_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2286_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v___x_2282_);
lean_dec(v_a_2279_);
lean_del_object(v___x_2276_);
lean_dec(v_snd_2274_);
lean_dec(v_a_2267_);
lean_dec_ref(v_rhs_2259_);
lean_dec_ref(v_tacticName_2258_);
lean_dec(v_binderName_2257_);
lean_dec_ref(v_body_2254_);
lean_dec(v_mvarId_2253_);
lean_dec_ref(v_binderType_2252_);
v_a_2332_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2284_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2284_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_del_object(v___x_2276_);
lean_dec(v_snd_2274_);
lean_dec(v_fst_2273_);
lean_dec(v_a_2267_);
lean_dec_ref(v_arg_2260_);
lean_dec_ref(v_rhs_2259_);
lean_dec_ref(v_tacticName_2258_);
lean_dec(v_binderName_2257_);
lean_dec_ref(v_body_2254_);
lean_dec(v_mvarId_2253_);
lean_dec_ref(v_binderType_2252_);
v_a_2340_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2278_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2278_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v___x_2270_);
lean_dec(v_a_2267_);
lean_dec_ref(v_arg_2260_);
lean_dec_ref(v_rhs_2259_);
lean_dec_ref(v_tacticName_2258_);
lean_dec(v_binderName_2257_);
lean_dec_ref(v_body_2254_);
lean_dec(v_mvarId_2253_);
lean_dec_ref(v_binderType_2252_);
v_a_2349_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2271_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2271_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_a_2267_);
lean_dec_ref(v_arg_2260_);
lean_dec_ref(v_rhs_2259_);
lean_dec_ref(v_tacticName_2258_);
lean_dec(v_binderName_2257_);
lean_dec_ref(v_body_2254_);
lean_dec(v_mvarId_2253_);
lean_dec_ref(v_binderType_2252_);
v_a_2357_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2268_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2268_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v_arg_2260_);
lean_dec_ref(v_rhs_2259_);
lean_dec_ref(v_tacticName_2258_);
lean_dec(v_binderName_2257_);
lean_dec_ref(v_body_2254_);
lean_dec(v_mvarId_2253_);
lean_dec_ref(v_binderType_2252_);
v_a_2365_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2266_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2266_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed(lean_object* v_binderType_2373_, lean_object* v_mvarId_2374_, lean_object* v_body_2375_, lean_object* v_domain_2376_, lean_object* v___x_2377_, lean_object* v_binderName_2378_, lean_object* v_tacticName_2379_, lean_object* v_rhs_2380_, lean_object* v_arg_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
uint8_t v_domain_boxed_2387_; uint8_t v___x_4187__boxed_2388_; lean_object* v_res_2389_; 
v_domain_boxed_2387_ = lean_unbox(v_domain_2376_);
v___x_4187__boxed_2388_ = lean_unbox(v___x_2377_);
v_res_2389_ = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(v_binderType_2373_, v_mvarId_2374_, v_body_2375_, v_domain_boxed_2387_, v___x_4187__boxed_2388_, v_binderName_2378_, v_tacticName_2379_, v_rhs_2380_, v_arg_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2390_, lean_object* v_b_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
lean_inc(v___y_2395_);
lean_inc_ref(v___y_2394_);
lean_inc(v___y_2393_);
lean_inc_ref(v___y_2392_);
v___x_2397_ = lean_apply_6(v_k_2390_, v_b_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, lean_box(0));
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2398_, lean_object* v_b_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(v_k_2398_, v_b_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(lean_object* v_name_2406_, uint8_t v_bi_2407_, lean_object* v_type_2408_, lean_object* v_k_2409_, uint8_t v_kind_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___f_2416_; lean_object* v___x_2417_; 
v___f_2416_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2416_, 0, v_k_2409_);
v___x_2417_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2406_, v_bi_2407_, v_type_2408_, v___f_2416_, v_kind_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
v_a_2426_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2417_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2417_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_2434_, lean_object* v_bi_2435_, lean_object* v_type_2436_, lean_object* v_k_2437_, lean_object* v_kind_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v_bi_boxed_2444_; uint8_t v_kind_boxed_2445_; lean_object* v_res_2446_; 
v_bi_boxed_2444_ = lean_unbox(v_bi_2435_);
v_kind_boxed_2445_ = lean_unbox(v_kind_2438_);
v_res_2446_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2434_, v_bi_boxed_2444_, v_type_2436_, v_k_2437_, v_kind_boxed_2445_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(lean_object* v_name_2447_, lean_object* v_type_2448_, lean_object* v_k_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = 0;
v___x_2456_ = 0;
v___x_2457_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2447_, v___x_2455_, v_type_2448_, v_k_2449_, v___x_2456_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg___boxed(lean_object* v_name_2458_, lean_object* v_type_2459_, lean_object* v_k_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2458_, v_type_2459_, v_k_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2466_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0));
v___x_2469_ = l_Lean_stringToMessageData(v___x_2468_);
return v___x_2469_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_2475_ = lean_unsigned_to_nat(33u);
v___x_2476_ = lean_unsigned_to_nat(158u);
v___x_2477_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4));
v___x_2478_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_2479_ = l_mkPanicMessageWithDecl(v___x_2478_, v___x_2477_, v___x_2476_, v___x_2475_, v___x_2474_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall(lean_object* v_tacticName_2480_, uint8_t v_domain_2481_, lean_object* v_mvarId_2482_, lean_object* v_lhs_2483_, lean_object* v_rhs_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
if (lean_obj_tag(v_lhs_2483_) == 7)
{
lean_object* v_binderName_2490_; lean_object* v_binderType_2491_; lean_object* v_body_2492_; uint8_t v_binderInfo_2493_; lean_object* v___y_2495_; 
v_binderName_2490_ = lean_ctor_get(v_lhs_2483_, 0);
lean_inc(v_binderName_2490_);
v_binderType_2491_ = lean_ctor_get(v_lhs_2483_, 1);
lean_inc_ref(v_binderType_2491_);
v_body_2492_ = lean_ctor_get(v_lhs_2483_, 2);
lean_inc_ref(v_body_2492_);
v_binderInfo_2493_ = lean_ctor_get_uint8(v_lhs_2483_, sizeof(void*)*3 + 8);
if (v_domain_2481_ == 0)
{
lean_object* v___x_2578_; 
lean_dec_ref_known(v_lhs_2483_, 3);
lean_inc(v_binderName_2490_);
v___x_2578_ = l_Lean_Core_mkFreshUserName(v_binderName_2490_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___x_2580_ = 1;
v___x_2581_ = lean_box(v_domain_2481_);
v___x_2582_ = lean_box(v___x_2580_);
lean_inc_ref(v_binderType_2491_);
v___f_2583_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed), 14, 8);
lean_closure_set(v___f_2583_, 0, v_binderType_2491_);
lean_closure_set(v___f_2583_, 1, v_mvarId_2482_);
lean_closure_set(v___f_2583_, 2, v_body_2492_);
lean_closure_set(v___f_2583_, 3, v___x_2581_);
lean_closure_set(v___f_2583_, 4, v___x_2582_);
lean_closure_set(v___f_2583_, 5, v_binderName_2490_);
lean_closure_set(v___f_2583_, 6, v_tacticName_2480_);
lean_closure_set(v___f_2583_, 7, v_rhs_2484_);
v___x_2584_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_a_2579_, v_binderType_2491_, v___f_2583_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
return v___x_2584_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2585_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2578_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2578_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
else
{
uint8_t v___x_2593_; 
v___x_2593_ = l_Lean_Expr_hasLooseBVars(v_body_2492_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
lean_dec_ref_known(v_lhs_2483_, 3);
lean_inc(v_mvarId_2482_);
v___x_2594_ = l_Lean_MVarId_getTag(v_mvarId_2482_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2596_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2596_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2491_, v_a_2595_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v_fst_2598_; lean_object* v_snd_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2652_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v_fst_2598_ = lean_ctor_get(v_a_2597_, 0);
v_snd_2599_ = lean_ctor_get(v_a_2597_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_a_2597_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2601_ = v_a_2597_;
v_isShared_2602_ = v_isSharedCheck_2652_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_snd_2599_);
lean_inc(v_fst_2598_);
lean_dec(v_a_2597_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2652_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; 
lean_inc_ref(v_body_2492_);
v___x_2603_ = l_Lean_Meta_mkEqRefl(v_body_2492_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v___x_2605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1));
v___x_2606_ = lean_unsigned_to_nat(2u);
v___x_2607_ = lean_mk_empty_array_with_capacity(v___x_2606_);
lean_inc(v_snd_2599_);
v___x_2608_ = lean_array_push(v___x_2607_, v_snd_2599_);
v___x_2609_ = lean_array_push(v___x_2608_, v_a_2604_);
v___x_2610_ = l_Lean_Meta_mkAppM(v___x_2605_, v___x_2609_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2482_, v_a_2611_, v_a_2486_);
lean_dec_ref(v___x_2612_);
v___x_2613_ = l_Lean_Expr_forallE___override(v_binderName_2490_, v_fst_2598_, v_body_2492_, v_binderInfo_2493_);
v___x_2614_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_2480_, v_rhs_2484_, v___x_2613_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2626_; 
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v___x_2614_, 0);
lean_dec(v_unused_2627_);
v___x_2616_ = v___x_2614_;
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
else
{
lean_dec(v___x_2614_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = l_Lean_Expr_mvarId_x21(v_snd_2599_);
lean_dec(v_snd_2599_);
v___x_2619_ = lean_box(0);
if (v_isShared_2602_ == 0)
{
lean_ctor_set_tag(v___x_2601_, 1);
lean_ctor_set(v___x_2601_, 1, v___x_2619_);
lean_ctor_set(v___x_2601_, 0, v___x_2618_);
v___x_2621_ = v___x_2601_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2621_);
v___x_2623_ = v___x_2616_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_del_object(v___x_2601_);
lean_dec(v_snd_2599_);
v_a_2628_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2614_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2614_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_del_object(v___x_2601_);
lean_dec(v_snd_2599_);
lean_dec(v_fst_2598_);
lean_dec_ref(v_body_2492_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2636_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2610_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2610_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_del_object(v___x_2601_);
lean_dec(v_snd_2599_);
lean_dec(v_fst_2598_);
lean_dec_ref(v_body_2492_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2644_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2603_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2603_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v_body_2492_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2653_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2596_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2596_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2661_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2594_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2594_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v___x_2669_; 
lean_inc_ref(v_body_2492_);
v___x_2669_ = l_Lean_Meta_isProp(v_body_2492_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; uint8_t v___x_2671_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
v___x_2671_ = lean_unbox(v_a_2670_);
lean_dec(v_a_2670_);
if (v___x_2671_ == 0)
{
lean_dec_ref_known(v_lhs_2483_, 3);
v___y_2495_ = v___x_2669_;
goto v___jp_2494_;
}
else
{
lean_object* v___x_2672_; 
lean_dec_ref_known(v___x_2669_, 1);
v___x_2672_ = l_Lean_Meta_isProp(v_lhs_2483_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
v___y_2495_ = v___x_2672_;
goto v___jp_2494_;
}
}
else
{
lean_dec_ref_known(v_lhs_2483_, 3);
v___y_2495_ = v___x_2669_;
goto v___jp_2494_;
}
}
}
v___jp_2494_:
{
if (lean_obj_tag(v___y_2495_) == 0)
{
lean_object* v_a_2496_; uint8_t v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___y_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___y_2495_, 1);
v___x_2497_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
v___x_2498_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2499_ = l_Lean_stringToMessageData(v_tacticName_2480_);
v___x_2500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1);
v___x_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2502_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; 
lean_inc(v_mvarId_2482_);
v___x_2504_ = l_Lean_MVarId_getTag(v_mvarId_2482_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
lean_inc_ref(v_binderType_2491_);
v___x_2506_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2491_, v_a_2505_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v_snd_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2552_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v_snd_2508_ = lean_ctor_get(v_a_2507_, 1);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_a_2507_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v_a_2507_, 0);
lean_dec(v_unused_2553_);
v___x_2510_ = v_a_2507_;
v_isShared_2511_ = v_isSharedCheck_2552_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_snd_2508_);
lean_dec(v_a_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2552_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2512_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3));
v___x_2513_ = 0;
v___x_2514_ = l_Lean_Expr_lam___override(v_binderName_2490_, v_binderType_2491_, v_body_2492_, v___x_2513_);
v___x_2515_ = lean_unsigned_to_nat(2u);
v___x_2516_ = lean_mk_empty_array_with_capacity(v___x_2515_);
lean_inc(v_snd_2508_);
v___x_2517_ = lean_array_push(v___x_2516_, v_snd_2508_);
v___x_2518_ = lean_array_push(v___x_2517_, v___x_2514_);
v___x_2519_ = l_Lean_Meta_mkAppM(v___x_2512_, v___x_2518_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2521_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_n(v_a_2520_, 2);
lean_dec_ref_known(v___x_2519_, 1);
v___x_2521_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2480_, v_rhs_2484_, v_a_2520_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2534_; 
lean_dec_ref_known(v___x_2521_, 1);
v___x_2522_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2482_, v_a_2520_, v_a_2486_);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2522_, 0);
lean_dec(v_unused_2535_);
v___x_2524_ = v___x_2522_;
v_isShared_2525_ = v_isSharedCheck_2534_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v___x_2522_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2534_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = l_Lean_Expr_mvarId_x21(v_snd_2508_);
lean_dec(v_snd_2508_);
v___x_2527_ = lean_box(0);
if (v_isShared_2511_ == 0)
{
lean_ctor_set_tag(v___x_2510_, 1);
lean_ctor_set(v___x_2510_, 1, v___x_2527_);
lean_ctor_set(v___x_2510_, 0, v___x_2526_);
v___x_2529_ = v___x_2510_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2531_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2529_);
v___x_2531_ = v___x_2524_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec(v_a_2520_);
lean_del_object(v___x_2510_);
lean_dec(v_snd_2508_);
lean_dec(v_mvarId_2482_);
v_a_2536_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2521_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2521_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_del_object(v___x_2510_);
lean_dec(v_snd_2508_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2544_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2519_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2519_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2554_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2506_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2506_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2562_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2504_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2504_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec(v_binderName_2490_);
lean_dec_ref(v_rhs_2484_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v_a_2570_ = lean_ctor_get(v___y_2495_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___y_2495_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___y_2495_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___y_2495_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec_ref(v_rhs_2484_);
lean_dec_ref(v_lhs_2483_);
lean_dec(v_mvarId_2482_);
lean_dec_ref(v_tacticName_2480_);
v___x_2673_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5);
v___x_2674_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v___x_2673_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
return v___x_2674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___boxed(lean_object* v_tacticName_2675_, lean_object* v_domain_2676_, lean_object* v_mvarId_2677_, lean_object* v_lhs_2678_, lean_object* v_rhs_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
uint8_t v_domain_boxed_2685_; lean_object* v_res_2686_; 
v_domain_boxed_2685_ = lean_unbox(v_domain_2676_);
v_res_2686_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_2675_, v_domain_boxed_2685_, v_mvarId_2677_, v_lhs_2678_, v_rhs_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_object* v_00_u03b1_2687_, lean_object* v_name_2688_, uint8_t v_bi_2689_, lean_object* v_type_2690_, lean_object* v_k_2691_, uint8_t v_kind_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2688_, v_bi_2689_, v_type_2690_, v_k_2691_, v_kind_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2699_, lean_object* v_name_2700_, lean_object* v_bi_2701_, lean_object* v_type_2702_, lean_object* v_k_2703_, lean_object* v_kind_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v_bi_boxed_2710_; uint8_t v_kind_boxed_2711_; lean_object* v_res_2712_; 
v_bi_boxed_2710_ = lean_unbox(v_bi_2701_);
v_kind_boxed_2711_ = lean_unbox(v_kind_2704_);
v_res_2712_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(v_00_u03b1_2699_, v_name_2700_, v_bi_boxed_2710_, v_type_2702_, v_k_2703_, v_kind_boxed_2711_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_object* v_00_u03b1_2713_, lean_object* v_name_2714_, lean_object* v_type_2715_, lean_object* v_k_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2714_, v_type_2715_, v_k_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_name_2724_, lean_object* v_type_2725_, lean_object* v_k_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(v_00_u03b1_2723_, v_name_2724_, v_type_2725_, v_k_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__0(lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = lean_nat_to_int(v_a_2733_);
return v___x_2734_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0));
v___x_2737_ = l_Lean_stringToMessageData(v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(lean_object* v_snd_2738_, lean_object* v_a_2739_, lean_object* v_____r_2740_, lean_object* v_fType_2741_, lean_object* v_j_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
if (lean_obj_tag(v_fType_2741_) == 7)
{
lean_object* v_body_2748_; uint8_t v_binderInfo_2749_; uint8_t v___x_2750_; 
v_body_2748_ = lean_ctor_get(v_fType_2741_, 2);
lean_inc_ref(v_body_2748_);
v_binderInfo_2749_ = lean_ctor_get_uint8(v_fType_2741_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fType_2741_, 3);
v___x_2750_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec(v_a_2739_);
lean_inc(v_j_2742_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_j_2742_);
lean_ctor_set(v___x_2751_, 1, v_snd_2738_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v_body_2748_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2755_ = lean_array_push(v_snd_2738_, v_a_2739_);
lean_inc(v_j_2742_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_j_2742_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_body_2748_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
return v___x_2759_;
}
}
else
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_dec(v_a_2739_);
v___x_2760_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1);
v___x_2761_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2760_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2771_; 
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v___x_2761_, 0);
lean_dec(v_unused_2772_);
v___x_2763_ = v___x_2761_;
v_isShared_2764_ = v_isSharedCheck_2771_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v___x_2761_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2771_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2769_; 
lean_inc(v_j_2742_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_j_2742_);
lean_ctor_set(v___x_2765_, 1, v_snd_2738_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_fType_2741_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2767_);
v___x_2769_ = v___x_2763_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_fType_2741_);
lean_dec(v_snd_2738_);
v_a_2773_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2761_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2761_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___boxed(lean_object* v_snd_2781_, lean_object* v_a_2782_, lean_object* v_____r_2783_, lean_object* v_fType_2784_, lean_object* v_j_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2781_, v_a_2782_, v_____r_2783_, v_fType_2784_, v_j_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v_j_2785_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(lean_object* v_upperBound_2792_, lean_object* v_xs_2793_, lean_object* v_a_2794_, lean_object* v_b_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___y_2802_; uint8_t v___x_2824_; 
v___x_2824_ = lean_nat_dec_lt(v_a_2794_, v_upperBound_2792_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
lean_dec(v_a_2794_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_b_2795_);
return v___x_2825_;
}
else
{
lean_object* v_snd_2826_; lean_object* v_fst_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v___y_2831_; uint8_t v___x_2843_; 
v_snd_2826_ = lean_ctor_get(v_b_2795_, 1);
lean_inc(v_snd_2826_);
v_fst_2827_ = lean_ctor_get(v_b_2795_, 0);
lean_inc(v_fst_2827_);
lean_dec_ref(v_b_2795_);
v_fst_2828_ = lean_ctor_get(v_snd_2826_, 0);
lean_inc(v_fst_2828_);
v_snd_2829_ = lean_ctor_get(v_snd_2826_, 1);
lean_inc(v_snd_2829_);
lean_dec(v_snd_2826_);
v___x_2843_ = l_Lean_Expr_isForall(v_fst_2827_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; uint8_t v_transparency_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2844_ = l_Lean_Meta_Context_config(v___y_2796_);
v_transparency_2845_ = lean_ctor_get_uint8(v___x_2844_, 9);
lean_dec_ref(v___x_2844_);
v___x_2846_ = 0;
v___x_2847_ = lean_expr_instantiate_rev_range(v_fst_2827_, v_fst_2828_, v_a_2794_, v_xs_2793_);
lean_dec(v_fst_2828_);
lean_dec(v_fst_2827_);
v___x_2848_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2845_, v___x_2846_);
if (v___x_2848_ == 0)
{
lean_object* v_keyedConfig_2849_; uint8_t v_trackZetaDelta_2850_; lean_object* v_zetaDeltaSet_2851_; lean_object* v_lctx_2852_; lean_object* v_localInstances_2853_; lean_object* v_defEqCtx_x3f_2854_; lean_object* v_synthPendingDepth_2855_; lean_object* v_customCanUnfoldPredicate_x3f_2856_; uint8_t v_univApprox_2857_; uint8_t v_inTypeClassResolution_2858_; uint8_t v_cacheInferType_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_keyedConfig_2849_ = lean_ctor_get(v___y_2796_, 0);
v_trackZetaDelta_2850_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7);
v_zetaDeltaSet_2851_ = lean_ctor_get(v___y_2796_, 1);
v_lctx_2852_ = lean_ctor_get(v___y_2796_, 2);
v_localInstances_2853_ = lean_ctor_get(v___y_2796_, 3);
v_defEqCtx_x3f_2854_ = lean_ctor_get(v___y_2796_, 4);
v_synthPendingDepth_2855_ = lean_ctor_get(v___y_2796_, 5);
v_customCanUnfoldPredicate_x3f_2856_ = lean_ctor_get(v___y_2796_, 6);
v_univApprox_2857_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2858_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7 + 2);
v_cacheInferType_2859_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2849_);
v___x_2860_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2846_, v_keyedConfig_2849_);
lean_inc(v_customCanUnfoldPredicate_x3f_2856_);
lean_inc(v_synthPendingDepth_2855_);
lean_inc(v_defEqCtx_x3f_2854_);
lean_inc_ref(v_localInstances_2853_);
lean_inc_ref(v_lctx_2852_);
lean_inc(v_zetaDeltaSet_2851_);
v___x_2861_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v_zetaDeltaSet_2851_);
lean_ctor_set(v___x_2861_, 2, v_lctx_2852_);
lean_ctor_set(v___x_2861_, 3, v_localInstances_2853_);
lean_ctor_set(v___x_2861_, 4, v_defEqCtx_x3f_2854_);
lean_ctor_set(v___x_2861_, 5, v_synthPendingDepth_2855_);
lean_ctor_set(v___x_2861_, 6, v_customCanUnfoldPredicate_x3f_2856_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*7, v_trackZetaDelta_2850_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*7 + 1, v_univApprox_2857_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2858_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*7 + 3, v_cacheInferType_2859_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
v___x_2862_ = lean_whnf(v___x_2847_, v___x_2861_, v___y_2797_, v___y_2798_, v___y_2799_);
v___y_2831_ = v___x_2862_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2863_; 
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
v___x_2863_ = lean_whnf(v___x_2847_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
v___y_2831_ = v___x_2863_;
goto v___jp_2830_;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_box(0);
lean_inc(v_a_2794_);
v___x_2865_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2829_, v_a_2794_, v___x_2864_, v_fst_2827_, v_fst_2828_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v_fst_2828_);
v___y_2802_ = v___x_2865_;
goto v___jp_2801_;
}
v___jp_2830_:
{
if (lean_obj_tag(v___y_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_a_2832_ = lean_ctor_get(v___y_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___y_2831_, 1);
v___x_2833_ = lean_box(0);
lean_inc(v_a_2794_);
v___x_2834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2829_, v_a_2794_, v___x_2833_, v_a_2832_, v_a_2794_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
v___y_2802_ = v___x_2834_;
goto v___jp_2801_;
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_snd_2829_);
lean_dec(v_a_2794_);
v_a_2835_ = lean_ctor_get(v___y_2831_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___y_2831_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___y_2831_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___y_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
v___jp_2801_:
{
if (lean_obj_tag(v___y_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2815_; 
v_a_2803_ = lean_ctor_get(v___y_2802_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___y_2802_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2805_ = v___y_2802_;
v_isShared_2806_ = v_isSharedCheck_2815_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___y_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2815_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
if (lean_obj_tag(v_a_2803_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; 
lean_dec(v_a_2794_);
v_a_2807_ = lean_ctor_get(v_a_2803_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v_a_2803_, 1);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v_a_2807_);
v___x_2809_ = v___x_2805_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_del_object(v___x_2805_);
v_a_2811_ = lean_ctor_get(v_a_2803_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v_a_2803_, 1);
v___x_2812_ = lean_unsigned_to_nat(1u);
v___x_2813_ = lean_nat_add(v_a_2794_, v___x_2812_);
lean_dec(v_a_2794_);
v_a_2794_ = v___x_2813_;
v_b_2795_ = v_a_2811_;
goto _start;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_a_2794_);
v_a_2816_ = lean_ctor_get(v___y_2802_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___y_2802_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___y_2802_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___y_2802_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object* v_upperBound_2866_, lean_object* v_xs_2867_, lean_object* v_a_2868_, lean_object* v_b_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_2866_, v_xs_2867_, v_a_2868_, v_b_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec_ref(v_xs_2867_);
lean_dec(v_upperBound_2866_);
return v_res_2875_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2));
v___x_2883_ = l_Lean_stringToMessageData(v___x_2882_);
return v___x_2883_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4));
v___x_2886_ = l_Lean_stringToMessageData(v___x_2885_);
return v___x_2886_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_unsigned_to_nat(0u);
v___x_2888_ = lean_nat_to_int(v___x_2887_);
return v___x_2888_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_to_int(v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8));
v___x_2893_ = l_Lean_stringToMessageData(v___x_2892_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object* v_tacticName_2894_, uint8_t v_explicit_2895_, lean_object* v_f_2896_, lean_object* v_xs_2897_, lean_object* v_i_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v___y_2905_; lean_object* v_lower_2906_; lean_object* v_upper_2907_; lean_object* v___y_2913_; lean_object* v_lower_2914_; lean_object* v_upper_2915_; 
if (v_explicit_2895_ == 0)
{
lean_object* v___x_2920_; 
lean_inc(v_a_2902_);
lean_inc_ref(v_a_2901_);
lean_inc(v_a_2900_);
lean_inc_ref(v_a_2899_);
lean_inc_ref(v_f_2896_);
v___x_2920_ = lean_infer_type(v_f_2896_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = lean_array_get_size(v_xs_2897_);
v___x_2923_ = lean_unsigned_to_nat(0u);
v___x_2924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1));
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2921_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v___x_2922_, v_xs_2897_, v___x_2923_, v___x_2925_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v_snd_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2986_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v_snd_2928_ = lean_ctor_get(v_a_2927_, 1);
v_isSharedCheck_2986_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v_a_2927_, 0);
lean_dec(v_unused_2987_);
v___x_2930_ = v_a_2927_;
v_isShared_2931_ = v_isSharedCheck_2986_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_snd_2928_);
lean_dec(v_a_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2986_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v_snd_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2984_; 
v_snd_2932_ = lean_ctor_get(v_snd_2928_, 1);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_snd_2928_);
if (v_isSharedCheck_2984_ == 0)
{
lean_object* v_unused_2985_; 
v_unused_2985_ = lean_ctor_get(v_snd_2928_, 0);
lean_dec(v_unused_2985_);
v___x_2934_ = v_snd_2928_;
v_isShared_2935_ = v_isSharedCheck_2984_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_snd_2932_);
lean_dec(v_snd_2928_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2984_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___y_2937_; lean_object* v___y_2945_; lean_object* v___x_2971_; lean_object* v___y_2973_; uint8_t v___x_2978_; 
v___x_2971_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_2978_ = lean_int_dec_lt(v___x_2971_, v_i_2898_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = lean_array_get_size(v_snd_2932_);
v___x_2980_ = lean_nat_to_int(v___x_2979_);
v___x_2981_ = lean_int_add(v_i_2898_, v___x_2980_);
lean_dec(v___x_2980_);
v___y_2973_ = v___x_2981_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_2983_ = lean_int_sub(v_i_2898_, v___x_2982_);
v___y_2973_ = v___x_2983_;
goto v___jp_2972_;
}
v___jp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2938_ = lean_nat_abs(v___y_2937_);
lean_dec(v___y_2937_);
v___x_2939_ = lean_array_get(v___x_2923_, v_snd_2932_, v___x_2938_);
lean_dec(v___x_2938_);
lean_dec(v_snd_2932_);
lean_inc(v___x_2939_);
lean_inc_ref(v_xs_2897_);
v___x_2940_ = l_Array_toSubarray___redArg(v_xs_2897_, v___x_2923_, v___x_2939_);
v___x_2941_ = l_Subarray_copy___redArg(v___x_2940_);
v___x_2942_ = l_Lean_mkAppN(v_f_2896_, v___x_2941_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = lean_nat_dec_le(v___x_2939_, v___x_2923_);
if (v___x_2943_ == 0)
{
v___y_2913_ = v___x_2942_;
v_lower_2914_ = v___x_2939_;
v_upper_2915_ = v___x_2922_;
goto v___jp_2912_;
}
else
{
lean_dec(v___x_2939_);
v___y_2913_ = v___x_2942_;
v_lower_2914_ = v___x_2923_;
v_upper_2915_ = v___x_2922_;
goto v___jp_2912_;
}
}
v___jp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_dec(v___y_2945_);
v___x_2946_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_2947_ = l_Lean_stringToMessageData(v_tacticName_2894_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 7);
lean_ctor_set(v___x_2934_, 1, v___x_2947_);
lean_ctor_set(v___x_2934_, 0, v___x_2946_);
v___x_2949_ = v___x_2934_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2970_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2952_; 
v___x_2950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
if (v_isShared_2931_ == 0)
{
lean_ctor_set_tag(v___x_2930_, 7);
lean_ctor_set(v___x_2930_, 1, v___x_2950_);
lean_ctor_set(v___x_2930_, 0, v___x_2949_);
v___x_2952_ = v___x_2930_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v___x_2953_ = lean_array_get_size(v_snd_2932_);
lean_dec(v_snd_2932_);
v___x_2954_ = l_Nat_reprFast(v___x_2953_);
v___x_2955_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2954_);
v___x_2956_ = l_Lean_MessageData_ofFormat(v___x_2955_);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2952_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2959_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2960_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
v___jp_2972_:
{
uint8_t v___x_2974_; 
v___x_2974_ = lean_int_dec_lt(v___y_2973_, v___x_2971_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2975_ = lean_array_get_size(v_snd_2932_);
v___x_2976_ = lean_nat_to_int(v___x_2975_);
v___x_2977_ = lean_int_dec_le(v___x_2976_, v___y_2973_);
lean_dec(v___x_2976_);
if (v___x_2977_ == 0)
{
lean_del_object(v___x_2934_);
lean_del_object(v___x_2930_);
lean_dec_ref(v_tacticName_2894_);
v___y_2937_ = v___y_2973_;
goto v___jp_2936_;
}
else
{
lean_dec_ref(v_xs_2897_);
lean_dec_ref(v_f_2896_);
v___y_2945_ = v___y_2973_;
goto v___jp_2944_;
}
}
else
{
lean_dec_ref(v_xs_2897_);
lean_dec_ref(v_f_2896_);
v___y_2945_ = v___y_2973_;
goto v___jp_2944_;
}
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec_ref(v_xs_2897_);
lean_dec_ref(v_f_2896_);
lean_dec_ref(v_tacticName_2894_);
v_a_2988_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2926_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2926_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v_xs_2897_);
lean_dec_ref(v_f_2896_);
lean_dec_ref(v_tacticName_2894_);
v_a_2996_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2920_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2920_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
else
{
lean_object* v___x_3004_; lean_object* v___y_3006_; lean_object* v___y_3014_; lean_object* v___x_3036_; lean_object* v___y_3038_; uint8_t v___x_3043_; 
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3036_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3043_ = lean_int_dec_lt(v___x_3036_, v_i_2898_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_array_get_size(v_xs_2897_);
v___x_3045_ = lean_nat_to_int(v___x_3044_);
v___x_3046_ = lean_int_add(v_i_2898_, v___x_3045_);
lean_dec(v___x_3045_);
v___y_3038_ = v___x_3046_;
goto v___jp_3037_;
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3048_ = lean_int_sub(v_i_2898_, v___x_3047_);
v___y_3038_ = v___x_3048_;
goto v___jp_3037_;
}
v___jp_3005_:
{
lean_object* v_idx_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_idx_3007_ = lean_nat_abs(v___y_3006_);
lean_dec(v___y_3006_);
lean_inc(v_idx_3007_);
lean_inc_ref(v_xs_2897_);
v___x_3008_ = l_Array_toSubarray___redArg(v_xs_2897_, v___x_3004_, v_idx_3007_);
v___x_3009_ = l_Subarray_copy___redArg(v___x_3008_);
v___x_3010_ = l_Lean_mkAppN(v_f_2896_, v___x_3009_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = lean_array_get_size(v_xs_2897_);
v___x_3012_ = lean_nat_dec_le(v_idx_3007_, v___x_3004_);
if (v___x_3012_ == 0)
{
v___y_2905_ = v___x_3010_;
v_lower_2906_ = v_idx_3007_;
v_upper_2907_ = v___x_3011_;
goto v___jp_2904_;
}
else
{
lean_dec(v_idx_3007_);
v___y_2905_ = v___x_3010_;
v_lower_2906_ = v___x_3004_;
v_upper_2907_ = v___x_3011_;
goto v___jp_2904_;
}
}
v___jp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v___y_3014_);
v___x_3015_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3016_ = l_Lean_stringToMessageData(v_tacticName_2894_);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_array_get_size(v_xs_2897_);
lean_dec_ref(v_xs_2897_);
v___x_3021_ = l_Nat_reprFast(v___x_3020_);
v___x_3022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
v___x_3023_ = l_Lean_MessageData_ofFormat(v___x_3022_);
v___x_3024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3019_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3024_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3026_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
v___jp_3037_:
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_int_dec_lt(v___y_3038_, v___x_3036_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3040_ = lean_array_get_size(v_xs_2897_);
v___x_3041_ = lean_nat_to_int(v___x_3040_);
v___x_3042_ = lean_int_dec_le(v___x_3041_, v___y_3038_);
lean_dec(v___x_3041_);
if (v___x_3042_ == 0)
{
lean_dec_ref(v_tacticName_2894_);
v___y_3006_ = v___y_3038_;
goto v___jp_3005_;
}
else
{
lean_dec_ref(v_f_2896_);
v___y_3014_ = v___y_3038_;
goto v___jp_3013_;
}
}
else
{
lean_dec_ref(v_f_2896_);
v___y_3014_ = v___y_3038_;
goto v___jp_3013_;
}
}
}
v___jp_2904_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2908_ = l_Array_toSubarray___redArg(v_xs_2897_, v_lower_2906_, v_upper_2907_);
v___x_2909_ = l_Subarray_copy___redArg(v___x_2908_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___y_2905_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
v___jp_2912_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2916_ = l_Array_toSubarray___redArg(v_xs_2897_, v_lower_2914_, v_upper_2915_);
v___x_2917_ = l_Subarray_copy___redArg(v___x_2916_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___y_2913_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object* v_tacticName_3049_, lean_object* v_explicit_3050_, lean_object* v_f_3051_, lean_object* v_xs_3052_, lean_object* v_i_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
uint8_t v_explicit_boxed_3059_; lean_object* v_res_3060_; 
v_explicit_boxed_3059_ = lean_unbox(v_explicit_3050_);
v_res_3060_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3049_, v_explicit_boxed_3059_, v_f_3051_, v_xs_3052_, v_i_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
lean_dec(v_i_3053_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object* v_upperBound_3061_, lean_object* v_xs_3062_, lean_object* v_inst_3063_, lean_object* v_R_3064_, lean_object* v_a_3065_, lean_object* v_b_3066_, lean_object* v_c_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_3061_, v_xs_3062_, v_a_3065_, v_b_3066_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object* v_upperBound_3074_, lean_object* v_xs_3075_, lean_object* v_inst_3076_, lean_object* v_R_3077_, lean_object* v_a_3078_, lean_object* v_b_3079_, lean_object* v_c_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(v_upperBound_3074_, v_xs_3075_, v_inst_3076_, v_R_3077_, v_a_3078_, v_b_3079_, v_c_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v_xs_3075_);
lean_dec(v_upperBound_3074_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object* v_tacticName_3087_, uint8_t v_explicit_3088_, lean_object* v_i_3089_, lean_object* v_mvarId_3090_, lean_object* v_snd_3091_, lean_object* v_x_3092_, lean_object* v_x_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
if (lean_obj_tag(v_x_3092_) == 5)
{
lean_object* v_fn_3100_; lean_object* v_arg_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_fn_3100_ = lean_ctor_get(v_x_3092_, 0);
lean_inc_ref(v_fn_3100_);
v_arg_3101_ = lean_ctor_get(v_x_3092_, 1);
lean_inc_ref(v_arg_3101_);
lean_dec_ref_known(v_x_3092_, 2);
v___x_3102_ = lean_array_set(v_x_3093_, v_x_3094_, v_arg_3101_);
v___x_3103_ = lean_unsigned_to_nat(1u);
v___x_3104_ = lean_nat_sub(v_x_3094_, v___x_3103_);
lean_dec(v_x_3094_);
v_x_3092_ = v_fn_3100_;
v_x_3093_ = v___x_3102_;
v_x_3094_ = v___x_3104_;
goto _start;
}
else
{
lean_object* v___x_3106_; 
lean_dec(v_x_3094_);
lean_inc_ref(v_tacticName_3087_);
v___x_3106_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3087_, v_explicit_3088_, v_x_3092_, v_x_3093_, v_i_3089_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v_fst_3108_; lean_object* v_snd_3109_; lean_object* v___x_3110_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v_fst_3108_ = lean_ctor_get(v_a_3107_, 0);
lean_inc(v_fst_3108_);
v_snd_3109_ = lean_ctor_get(v_a_3107_, 1);
lean_inc(v_snd_3109_);
lean_dec(v_a_3107_);
lean_inc(v_mvarId_3090_);
v___x_3110_ = l_Lean_MVarId_getTag(v_mvarId_3090_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
lean_inc_ref(v_tacticName_3087_);
v___x_3112_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_3087_, v_a_3111_, v_fst_3108_, v_snd_3109_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v_snd_3114_; lean_object* v_fst_3115_; lean_object* v_fst_3116_; lean_object* v_snd_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3143_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v_snd_3114_ = lean_ctor_get(v_a_3113_, 1);
lean_inc(v_snd_3114_);
v_fst_3115_ = lean_ctor_get(v_a_3113_, 0);
lean_inc(v_fst_3115_);
lean_dec(v_a_3113_);
v_fst_3116_ = lean_ctor_get(v_snd_3114_, 0);
v_snd_3117_ = lean_ctor_get(v_snd_3114_, 1);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_snd_3114_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3119_ = v_snd_3114_;
v_isShared_3120_ = v_isSharedCheck_3143_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_snd_3117_);
lean_inc(v_fst_3116_);
lean_dec(v_snd_3114_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3143_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; 
lean_inc(v_fst_3115_);
v___x_3121_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_3087_, v_snd_3091_, v_fst_3115_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref_known(v___x_3121_, 1);
v___x_3122_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_3090_, v_fst_3115_, v___y_3096_);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___x_3122_, 0);
lean_dec(v_unused_3134_);
v___x_3124_ = v___x_3122_;
v_isShared_3125_ = v_isSharedCheck_3133_;
goto v_resetjp_3123_;
}
else
{
lean_dec(v___x_3122_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3133_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_array_to_list(v_snd_3117_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set_tag(v___x_3119_, 1);
lean_ctor_set(v___x_3119_, 1, v___x_3126_);
v___x_3128_ = v___x_3119_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_fst_3116_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3128_);
v___x_3130_ = v___x_3124_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_del_object(v___x_3119_);
lean_dec(v_snd_3117_);
lean_dec(v_fst_3116_);
lean_dec(v_fst_3115_);
lean_dec(v_mvarId_3090_);
v_a_3135_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3121_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3121_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v_snd_3091_);
lean_dec(v_mvarId_3090_);
lean_dec_ref(v_tacticName_3087_);
v_a_3144_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3112_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3112_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_snd_3109_);
lean_dec(v_fst_3108_);
lean_dec_ref(v_snd_3091_);
lean_dec(v_mvarId_3090_);
lean_dec_ref(v_tacticName_3087_);
v_a_3152_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3110_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3110_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref(v_snd_3091_);
lean_dec(v_mvarId_3090_);
lean_dec_ref(v_tacticName_3087_);
v_a_3160_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3106_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3106_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object* v_tacticName_3168_, lean_object* v_explicit_3169_, lean_object* v_i_3170_, lean_object* v_mvarId_3171_, lean_object* v_snd_3172_, lean_object* v_x_3173_, lean_object* v_x_3174_, lean_object* v_x_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
uint8_t v_explicit_boxed_3181_; lean_object* v_res_3182_; 
v_explicit_boxed_3181_ = lean_unbox(v_explicit_3169_);
v_res_3182_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3168_, v_explicit_boxed_3181_, v_i_3170_, v_mvarId_3171_, v_snd_3172_, v_x_3173_, v_x_3174_, v_x_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
lean_dec(v_i_3170_);
return v_res_3182_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = lean_unsigned_to_nat(2u);
v___x_3184_ = lean_nat_to_int(v___x_3183_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3186_ = lean_int_neg(v___x_3185_);
return v___x_3186_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2));
v___x_3189_ = l_Lean_stringToMessageData(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4));
v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object* v_mvarId_3193_, lean_object* v_tacticName_3194_, uint8_t v_explicit_3195_, lean_object* v_i_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; 
lean_inc(v_mvarId_3193_);
v___x_3202_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_3193_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v_fst_3204_; lean_object* v_snd_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3264_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 1);
v_fst_3204_ = lean_ctor_get(v_a_3203_, 0);
v_snd_3205_ = lean_ctor_get(v_a_3203_, 1);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_3203_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3207_ = v_a_3203_;
v_isShared_3208_ = v_isSharedCheck_3264_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_snd_3205_);
lean_inc(v_fst_3204_);
lean_dec(v_a_3203_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3264_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v_a_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; uint8_t v___y_3242_; 
v___x_3209_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_3204_, v___y_3198_);
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref(v___x_3209_);
v___x_3211_ = l_Lean_Expr_cleanupAnnotations(v_a_3210_);
v___x_3212_ = l_Lean_Expr_isForall(v___x_3211_);
if (v___x_3212_ == 0)
{
uint8_t v___x_3245_; 
lean_del_object(v___x_3207_);
v___x_3245_ = l_Lean_Expr_isApp(v___x_3211_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v_snd_3205_);
lean_dec(v_mvarId_3193_);
v___x_3246_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3247_ = l_Lean_stringToMessageData(v_tacticName_3194_);
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3246_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = l_Lean_indentExpr(v___x_3211_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3252_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
return v___x_3253_;
}
else
{
lean_object* v_dummy_3254_; lean_object* v_nargs_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_dummy_3254_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_3255_ = l_Lean_Expr_getAppNumArgs(v___x_3211_);
lean_inc(v_nargs_3255_);
v___x_3256_ = lean_mk_array(v_nargs_3255_, v_dummy_3254_);
v___x_3257_ = lean_unsigned_to_nat(1u);
v___x_3258_ = lean_nat_sub(v_nargs_3255_, v___x_3257_);
lean_dec(v_nargs_3255_);
v___x_3259_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3194_, v_explicit_3195_, v_i_3196_, v_mvarId_3193_, v_snd_3205_, v___x_3211_, v___x_3256_, v___x_3258_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
return v___x_3259_;
}
}
else
{
lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3260_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3261_ = lean_int_dec_lt(v_i_3196_, v___x_3260_);
if (v___x_3261_ == 0)
{
lean_object* v___x_3262_; uint8_t v___x_3263_; 
v___x_3262_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3263_ = lean_int_dec_eq(v_i_3196_, v___x_3262_);
v___y_3242_ = v___x_3263_;
goto v___jp_3241_;
}
else
{
v___y_3242_ = v___x_3212_;
goto v___jp_3241_;
}
}
v___jp_3213_:
{
lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3218_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3219_ = lean_int_dec_eq(v_i_3196_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; uint8_t v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3221_ = lean_int_dec_eq(v_i_3196_, v___x_3220_);
v___x_3222_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3194_, v___x_3221_, v_mvarId_3193_, v___x_3211_, v_snd_3205_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3194_, v___x_3212_, v_mvarId_3193_, v___x_3211_, v_snd_3205_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
return v___x_3223_;
}
}
v___jp_3224_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3225_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3226_ = l_Lean_stringToMessageData(v_tacticName_3194_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set_tag(v___x_3207_, 7);
lean_ctor_set(v___x_3207_, 1, v___x_3226_);
lean_ctor_set(v___x_3207_, 0, v___x_3225_);
v___x_3228_ = v___x_3207_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
v___x_3229_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3);
v___x_3230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3230_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
v___jp_3241_:
{
if (v___y_3242_ == 0)
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3244_ = lean_int_dec_lt(v___x_3243_, v_i_3196_);
if (v___x_3244_ == 0)
{
lean_del_object(v___x_3207_);
v___y_3214_ = v___y_3197_;
v___y_3215_ = v___y_3198_;
v___y_3216_ = v___y_3199_;
v___y_3217_ = v___y_3200_;
goto v___jp_3213_;
}
else
{
lean_dec_ref(v___x_3211_);
lean_dec(v_snd_3205_);
lean_dec(v_mvarId_3193_);
goto v___jp_3224_;
}
}
else
{
lean_dec_ref(v___x_3211_);
lean_dec(v_snd_3205_);
lean_dec(v_mvarId_3193_);
goto v___jp_3224_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref(v_tacticName_3194_);
lean_dec(v_mvarId_3193_);
v_a_3265_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3202_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3202_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object* v_mvarId_3273_, lean_object* v_tacticName_3274_, lean_object* v_explicit_3275_, lean_object* v_i_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
uint8_t v_explicit_boxed_3282_; lean_object* v_res_3283_; 
v_explicit_boxed_3282_ = lean_unbox(v_explicit_3275_);
v_res_3283_ = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(v_mvarId_3273_, v_tacticName_3274_, v_explicit_boxed_3282_, v_i_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v_i_3276_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object* v_tacticName_3284_, lean_object* v_mvarId_3285_, lean_object* v_i_3286_, uint8_t v_explicit_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3293_; lean_object* v___f_3294_; lean_object* v___x_3295_; 
v___x_3293_ = lean_box(v_explicit_3287_);
lean_inc(v_mvarId_3285_);
v___f_3294_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3294_, 0, v_mvarId_3285_);
lean_closure_set(v___f_3294_, 1, v_tacticName_3284_);
lean_closure_set(v___f_3294_, 2, v___x_3293_);
lean_closure_set(v___f_3294_, 3, v_i_3286_);
v___x_3295_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_3285_, v___f_3294_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object* v_tacticName_3296_, lean_object* v_mvarId_3297_, lean_object* v_i_3298_, lean_object* v_explicit_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_){
_start:
{
uint8_t v_explicit_boxed_3305_; lean_object* v_res_3306_; 
v_explicit_boxed_3305_ = lean_unbox(v_explicit_3299_);
v_res_3306_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3296_, v_mvarId_3297_, v_i_3298_, v_explicit_boxed_3305_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object* v_tacticName_3307_, lean_object* v_i_3308_, uint8_t v_explicit_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_){
_start:
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3317_ = lean_int_dec_eq(v_i_3308_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3307_, v_a_3319_, v_i_3308_, v_explicit_3309_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3322_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref_known(v___x_3320_, 1);
v___x_3322_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3321_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
return v___x_3322_;
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
v_a_3323_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3320_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3320_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec(v_i_3308_);
lean_dec_ref(v_tacticName_3307_);
v_a_3331_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3318_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3318_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
else
{
lean_object* v___x_3339_; 
lean_dec(v_i_3308_);
lean_dec_ref(v_tacticName_3307_);
v___x_3339_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_a_3340_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_a_3342_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3344_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_);
return v___x_3345_;
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
v_a_3346_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3341_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3341_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
v_a_3354_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3339_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3339_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object* v_tacticName_3362_, lean_object* v_i_3363_, lean_object* v_explicit_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
uint8_t v_explicit_boxed_3371_; lean_object* v_res_3372_; 
v_explicit_boxed_3371_ = lean_unbox(v_explicit_3364_);
v_res_3372_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3362_, v_i_3363_, v_explicit_boxed_3371_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object* v_tacticName_3373_, lean_object* v_i_3374_, uint8_t v_explicit_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3373_, v_i_3374_, v_explicit_3375_, v_a_3377_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object* v_tacticName_3386_, lean_object* v_i_3387_, lean_object* v_explicit_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
uint8_t v_explicit_boxed_3398_; lean_object* v_res_3399_; 
v_explicit_boxed_3398_ = lean_unbox(v_explicit_3388_);
v_res_3399_ = l_Lean_Elab_Tactic_Conv_evalArg(v_tacticName_3386_, v_i_3387_, v_explicit_boxed_3398_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec(v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec_ref(v_a_3391_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
return v_res_3399_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_box(0);
v___x_3401_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3400_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg(){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0);
v___x_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object* v_00_u03b1_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object* v_00_u03b1_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(v_00_u03b1_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object* v_stx_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3457_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_3458_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
lean_inc(v_stx_3447_);
v___x_3459_ = l_Lean_Syntax_isOfKind(v_stx_3447_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
lean_dec(v_stx_3447_);
v___x_3460_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3460_;
}
else
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3487_; lean_object* v_neg_x3f_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; 
v___x_3461_ = lean_unsigned_to_nat(1u);
v___x_3462_ = l_Lean_Syntax_getArg(v_stx_3447_, v___x_3461_);
lean_dec(v_stx_3447_);
v___x_3463_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__3));
lean_inc(v___x_3462_);
v___x_3464_ = l_Lean_Syntax_isOfKind(v___x_3462_, v___x_3463_);
if (v___x_3464_ == 0)
{
lean_object* v___x_3505_; 
lean_dec(v___x_3462_);
v___x_3505_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; lean_object* v_tk_x3f_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3506_ = lean_unsigned_to_nat(0u);
v___x_3524_ = l_Lean_Syntax_getArg(v___x_3462_, v___x_3506_);
v___x_3525_ = l_Lean_Syntax_isNone(v___x_3524_);
if (v___x_3525_ == 0)
{
uint8_t v___x_3526_; 
lean_inc(v___x_3524_);
v___x_3526_ = l_Lean_Syntax_matchesNull(v___x_3524_, v___x_3461_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
lean_dec(v___x_3524_);
lean_dec(v___x_3462_);
v___x_3527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3527_;
}
else
{
lean_object* v_tk_x3f_3528_; lean_object* v___x_3529_; 
v_tk_x3f_3528_ = l_Lean_Syntax_getArg(v___x_3524_, v___x_3506_);
lean_dec(v___x_3524_);
v___x_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3529_, 0, v_tk_x3f_3528_);
v_tk_x3f_3508_ = v___x_3529_;
v___y_3509_ = v_a_3448_;
v___y_3510_ = v_a_3449_;
v___y_3511_ = v_a_3450_;
v___y_3512_ = v_a_3451_;
v___y_3513_ = v_a_3452_;
v___y_3514_ = v_a_3453_;
v___y_3515_ = v_a_3454_;
v___y_3516_ = v_a_3455_;
goto v___jp_3507_;
}
}
else
{
lean_object* v___x_3530_; 
lean_dec(v___x_3524_);
v___x_3530_ = lean_box(0);
v_tk_x3f_3508_ = v___x_3530_;
v___y_3509_ = v_a_3448_;
v___y_3510_ = v_a_3449_;
v___y_3511_ = v_a_3450_;
v___y_3512_ = v_a_3451_;
v___y_3513_ = v_a_3452_;
v___y_3514_ = v_a_3453_;
v___y_3515_ = v_a_3454_;
v___y_3516_ = v_a_3455_;
goto v___jp_3507_;
}
v___jp_3507_:
{
lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3517_ = l_Lean_Syntax_getArg(v___x_3462_, v___x_3461_);
v___x_3518_ = l_Lean_Syntax_isNone(v___x_3517_);
if (v___x_3518_ == 0)
{
uint8_t v___x_3519_; 
lean_inc(v___x_3517_);
v___x_3519_ = l_Lean_Syntax_matchesNull(v___x_3517_, v___x_3461_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; 
lean_dec(v___x_3517_);
lean_dec(v_tk_x3f_3508_);
lean_dec(v___x_3462_);
v___x_3520_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3520_;
}
else
{
lean_object* v_neg_x3f_3521_; lean_object* v___x_3522_; 
v_neg_x3f_3521_ = l_Lean_Syntax_getArg(v___x_3517_, v___x_3506_);
lean_dec(v___x_3517_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_neg_x3f_3521_);
v___y_3487_ = v_tk_x3f_3508_;
v_neg_x3f_3488_ = v___x_3522_;
v___y_3489_ = v___y_3509_;
v___y_3490_ = v___y_3510_;
v___y_3491_ = v___y_3511_;
v___y_3492_ = v___y_3512_;
v___y_3493_ = v___y_3513_;
v___y_3494_ = v___y_3514_;
v___y_3495_ = v___y_3515_;
v___y_3496_ = v___y_3516_;
goto v___jp_3486_;
}
}
else
{
lean_object* v___x_3523_; 
lean_dec(v___x_3517_);
v___x_3523_ = lean_box(0);
v___y_3487_ = v_tk_x3f_3508_;
v_neg_x3f_3488_ = v___x_3523_;
v___y_3489_ = v___y_3509_;
v___y_3490_ = v___y_3510_;
v___y_3491_ = v___y_3511_;
v___y_3492_ = v___y_3512_;
v___y_3493_ = v___y_3513_;
v___y_3494_ = v___y_3514_;
v___y_3495_ = v___y_3515_;
v___y_3496_ = v___y_3516_;
goto v___jp_3486_;
}
}
}
v___jp_3465_:
{
if (lean_obj_tag(v___y_3468_) == 0)
{
uint8_t v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = 0;
v___x_3474_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3457_, v___y_3472_, v___x_3473_, v___y_3470_, v___y_3467_, v___y_3471_, v___y_3466_, v___y_3469_);
return v___x_3474_;
}
else
{
lean_object* v___x_3475_; 
lean_dec_ref_known(v___y_3468_, 1);
v___x_3475_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3457_, v___y_3472_, v___x_3464_, v___y_3470_, v___y_3467_, v___y_3471_, v___y_3466_, v___y_3469_);
return v___x_3475_;
}
}
v___jp_3476_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = l_Lean_TSyntax_getNat(v___y_3477_);
lean_dec(v___y_3477_);
v___x_3485_ = lean_nat_to_int(v___x_3484_);
v___y_3466_ = v___y_3478_;
v___y_3467_ = v___y_3479_;
v___y_3468_ = v___y_3480_;
v___y_3469_ = v___y_3481_;
v___y_3470_ = v___y_3482_;
v___y_3471_ = v___y_3483_;
v___y_3472_ = v___x_3485_;
goto v___jp_3465_;
}
v___jp_3486_:
{
lean_object* v___x_3497_; lean_object* v_i_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3497_ = lean_unsigned_to_nat(2u);
v_i_3498_ = l_Lean_Syntax_getArg(v___x_3462_, v___x_3497_);
lean_dec(v___x_3462_);
v___x_3499_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__5));
lean_inc(v_i_3498_);
v___x_3500_ = l_Lean_Syntax_isOfKind(v_i_3498_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v_i_3498_);
lean_dec(v_neg_x3f_3488_);
lean_dec(v___y_3487_);
v___x_3501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3501_;
}
else
{
if (lean_obj_tag(v_neg_x3f_3488_) == 0)
{
v___y_3477_ = v_i_3498_;
v___y_3478_ = v___y_3495_;
v___y_3479_ = v___y_3493_;
v___y_3480_ = v___y_3487_;
v___y_3481_ = v___y_3496_;
v___y_3482_ = v___y_3490_;
v___y_3483_ = v___y_3494_;
goto v___jp_3476_;
}
else
{
lean_dec_ref_known(v_neg_x3f_3488_, 1);
if (v___x_3464_ == 0)
{
v___y_3477_ = v_i_3498_;
v___y_3478_ = v___y_3495_;
v___y_3479_ = v___y_3493_;
v___y_3480_ = v___y_3487_;
v___y_3481_ = v___y_3496_;
v___y_3482_ = v___y_3490_;
v___y_3483_ = v___y_3494_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3502_ = l_Lean_TSyntax_getNat(v_i_3498_);
lean_dec(v_i_3498_);
v___x_3503_ = lean_nat_to_int(v___x_3502_);
v___x_3504_ = lean_int_neg(v___x_3503_);
lean_dec(v___x_3503_);
v___y_3466_ = v___y_3495_;
v___y_3467_ = v___y_3493_;
v___y_3468_ = v___y_3487_;
v___y_3469_ = v___y_3496_;
v___y_3470_ = v___y_3490_;
v___y_3471_ = v___y_3494_;
v___y_3472_ = v___x_3504_;
goto v___jp_3465_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object* v_stx_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_Lean_Elab_Tactic_Conv_elabArg(v_stx_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1(){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3550_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3551_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1));
v___x_3553_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_elabArg___boxed), 10, 0);
v___x_3554_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3550_, v___x_3551_, v___x_3552_, v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; 
v___x_3564_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0));
v___x_3565_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3566_ = 0;
v___x_3567_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3564_, v___x_3565_, v___x_3566_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object* v_x_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3577_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object* v_x_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Lean_Elab_Tactic_Conv_evalLhs(v_x_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
lean_dec(v_x_3586_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1(){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3611_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0));
v___x_3613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3614_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLhs___boxed), 10, 0);
v___x_3615_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3611_, v___x_3612_, v___x_3613_, v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object* v_a_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3(){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3645_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6));
v___x_3646_ = l_Lean_addBuiltinDeclarationRanges(v___x_3644_, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
return v_res_3648_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3650_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3651_ = lean_int_neg(v___x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; lean_object* v___x_3661_; 
v___x_3658_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0));
v___x_3659_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1, &l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1);
v___x_3660_ = 0;
v___x_3661_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3658_, v___x_3659_, v___x_3660_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_);
lean_dec(v_a_3666_);
lean_dec_ref(v_a_3665_);
lean_dec(v_a_3664_);
lean_dec_ref(v_a_3663_);
lean_dec(v_a_3662_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object* v_x_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3671_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object* v_x_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_Elab_Tactic_Conv_evalRhs(v_x_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec(v_x_3680_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1(){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3705_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0));
v___x_3707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3708_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRhs___boxed), 10, 0);
v___x_3709_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3705_, v___x_3706_, v___x_3707_, v___x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3(){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6));
v___x_3740_ = l_Lean_addBuiltinDeclarationRanges(v___x_3738_, v___x_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object* v_a_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object* v_e_3743_, lean_object* v___y_3744_){
_start:
{
uint8_t v___x_3746_; 
v___x_3746_ = l_Lean_Expr_hasMVar(v_e_3743_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v_e_3743_);
return v___x_3747_;
}
else
{
lean_object* v___x_3748_; lean_object* v_mctx_3749_; lean_object* v___x_3750_; lean_object* v_fst_3751_; lean_object* v_snd_3752_; lean_object* v___x_3753_; lean_object* v_cache_3754_; lean_object* v_zetaDeltaFVarIds_3755_; lean_object* v_postponed_3756_; lean_object* v_diag_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3766_; 
v___x_3748_ = lean_st_ref_get(v___y_3744_);
v_mctx_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc_ref(v_mctx_3749_);
lean_dec(v___x_3748_);
v___x_3750_ = l_Lean_instantiateMVarsCore(v_mctx_3749_, v_e_3743_);
v_fst_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_fst_3751_);
v_snd_3752_ = lean_ctor_get(v___x_3750_, 1);
lean_inc(v_snd_3752_);
lean_dec_ref(v___x_3750_);
v___x_3753_ = lean_st_ref_take(v___y_3744_);
v_cache_3754_ = lean_ctor_get(v___x_3753_, 1);
v_zetaDeltaFVarIds_3755_ = lean_ctor_get(v___x_3753_, 2);
v_postponed_3756_ = lean_ctor_get(v___x_3753_, 3);
v_diag_3757_ = lean_ctor_get(v___x_3753_, 4);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3766_ == 0)
{
lean_object* v_unused_3767_; 
v_unused_3767_ = lean_ctor_get(v___x_3753_, 0);
lean_dec(v_unused_3767_);
v___x_3759_ = v___x_3753_;
v_isShared_3760_ = v_isSharedCheck_3766_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_diag_3757_);
lean_inc(v_postponed_3756_);
lean_inc(v_zetaDeltaFVarIds_3755_);
lean_inc(v_cache_3754_);
lean_dec(v___x_3753_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3766_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_snd_3752_);
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_snd_3752_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_cache_3754_);
lean_ctor_set(v_reuseFailAlloc_3765_, 2, v_zetaDeltaFVarIds_3755_);
lean_ctor_set(v_reuseFailAlloc_3765_, 3, v_postponed_3756_);
lean_ctor_set(v_reuseFailAlloc_3765_, 4, v_diag_3757_);
v___x_3762_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_st_ref_put(v___y_3744_, v___x_3762_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_fst_3751_);
return v___x_3764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object* v_e_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3768_, v___y_3769_);
lean_dec(v___y_3769_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object* v_e_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3772_, v___y_3778_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object* v_e_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(v_e_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object* v_x_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; 
lean_inc(v___y_3798_);
lean_inc_ref(v___y_3797_);
lean_inc(v___y_3796_);
lean_inc_ref(v___y_3795_);
v___x_3804_ = lean_apply_9(v_x_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, lean_box(0));
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object* v_x_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(v_x_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object* v_mvarId_3816_, lean_object* v_x_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___f_3827_; lean_object* v___x_3828_; 
lean_inc(v___y_3821_);
lean_inc_ref(v___y_3820_);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3818_);
v___f_3827_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3827_, 0, v_x_3817_);
lean_closure_set(v___f_3827_, 1, v___y_3818_);
lean_closure_set(v___f_3827_, 2, v___y_3819_);
lean_closure_set(v___f_3827_, 3, v___y_3820_);
lean_closure_set(v___f_3827_, 4, v___y_3821_);
v___x_3828_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3816_, v___f_3827_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
if (lean_obj_tag(v___x_3828_) == 0)
{
return v___x_3828_;
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3828_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object* v_mvarId_3837_, lean_object* v_x_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3837_, v_x_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object* v_00_u03b1_3849_, lean_object* v_mvarId_3850_, lean_object* v_x_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3850_, v_x_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object* v_00_u03b1_3862_, lean_object* v_mvarId_3863_, lean_object* v_x_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(v_00_u03b1_3862_, v_mvarId_3863_, v_x_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object* v_msg_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v_ref_3881_; lean_object* v___x_3882_; lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3891_; 
v_ref_3881_ = lean_ctor_get(v___y_3878_, 2);
v___x_3882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3891_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; lean_object* v___x_3889_; 
lean_inc(v_ref_3881_);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v_ref_3881_);
lean_ctor_set(v___x_3887_, 1, v_a_3883_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set_tag(v___x_3885_, 1);
lean_ctor_set(v___x_3885_, 0, v___x_3887_);
v___x_3889_ = v___x_3885_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object* v_msg_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object* v_mvarId_3899_, lean_object* v_val_3900_, lean_object* v___y_3901_){
_start:
{
lean_object* v___x_3903_; lean_object* v_mctx_3904_; lean_object* v_cache_3905_; lean_object* v_zetaDeltaFVarIds_3906_; lean_object* v_postponed_3907_; lean_object* v_diag_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3937_; 
v___x_3903_ = lean_st_ref_take(v___y_3901_);
v_mctx_3904_ = lean_ctor_get(v___x_3903_, 0);
v_cache_3905_ = lean_ctor_get(v___x_3903_, 1);
v_zetaDeltaFVarIds_3906_ = lean_ctor_get(v___x_3903_, 2);
v_postponed_3907_ = lean_ctor_get(v___x_3903_, 3);
v_diag_3908_ = lean_ctor_get(v___x_3903_, 4);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3910_ = v___x_3903_;
v_isShared_3911_ = v_isSharedCheck_3937_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_diag_3908_);
lean_inc(v_postponed_3907_);
lean_inc(v_zetaDeltaFVarIds_3906_);
lean_inc(v_cache_3905_);
lean_inc(v_mctx_3904_);
lean_dec(v___x_3903_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3937_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v_depth_3912_; lean_object* v_levelAssignDepth_3913_; lean_object* v_lmvarCounter_3914_; lean_object* v_mvarCounter_3915_; lean_object* v_lDecls_3916_; lean_object* v_decls_3917_; lean_object* v_userNames_3918_; lean_object* v_lAssignment_3919_; lean_object* v_eAssignment_3920_; lean_object* v_dAssignment_3921_; lean_object* v_instanceTypedMVars_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3936_; 
v_depth_3912_ = lean_ctor_get(v_mctx_3904_, 0);
v_levelAssignDepth_3913_ = lean_ctor_get(v_mctx_3904_, 1);
v_lmvarCounter_3914_ = lean_ctor_get(v_mctx_3904_, 2);
v_mvarCounter_3915_ = lean_ctor_get(v_mctx_3904_, 3);
v_lDecls_3916_ = lean_ctor_get(v_mctx_3904_, 4);
v_decls_3917_ = lean_ctor_get(v_mctx_3904_, 5);
v_userNames_3918_ = lean_ctor_get(v_mctx_3904_, 6);
v_lAssignment_3919_ = lean_ctor_get(v_mctx_3904_, 7);
v_eAssignment_3920_ = lean_ctor_get(v_mctx_3904_, 8);
v_dAssignment_3921_ = lean_ctor_get(v_mctx_3904_, 9);
v_instanceTypedMVars_3922_ = lean_ctor_get(v_mctx_3904_, 10);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_mctx_3904_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3924_ = v_mctx_3904_;
v_isShared_3925_ = v_isSharedCheck_3936_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_instanceTypedMVars_3922_);
lean_inc(v_dAssignment_3921_);
lean_inc(v_eAssignment_3920_);
lean_inc(v_lAssignment_3919_);
lean_inc(v_userNames_3918_);
lean_inc(v_decls_3917_);
lean_inc(v_lDecls_3916_);
lean_inc(v_mvarCounter_3915_);
lean_inc(v_lmvarCounter_3914_);
lean_inc(v_levelAssignDepth_3913_);
lean_inc(v_depth_3912_);
lean_dec(v_mctx_3904_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3936_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_3920_, v_mvarId_3899_, v_val_3900_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 8, v___x_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_depth_3912_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_levelAssignDepth_3913_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_lmvarCounter_3914_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v_mvarCounter_3915_);
lean_ctor_set(v_reuseFailAlloc_3935_, 4, v_lDecls_3916_);
lean_ctor_set(v_reuseFailAlloc_3935_, 5, v_decls_3917_);
lean_ctor_set(v_reuseFailAlloc_3935_, 6, v_userNames_3918_);
lean_ctor_set(v_reuseFailAlloc_3935_, 7, v_lAssignment_3919_);
lean_ctor_set(v_reuseFailAlloc_3935_, 8, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3935_, 9, v_dAssignment_3921_);
lean_ctor_set(v_reuseFailAlloc_3935_, 10, v_instanceTypedMVars_3922_);
v___x_3928_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3930_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3928_);
v___x_3930_ = v___x_3910_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_cache_3905_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_zetaDeltaFVarIds_3906_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v_postponed_3907_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v_diag_3908_);
v___x_3930_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3931_ = lean_st_ref_put(v___y_3901_, v___x_3930_);
v___x_3932_ = lean_box(0);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object* v_mvarId_3938_, lean_object* v_val_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_3938_, v_val_3939_, v___y_3940_);
lean_dec(v___y_3940_);
return v_res_3942_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1));
v___x_3946_ = l_Lean_stringToMessageData(v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object* v_a_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v___x_3957_; 
lean_inc(v_a_3947_);
v___x_3957_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_3947_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v_fst_3959_; lean_object* v_snd_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_4012_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v_fst_3959_ = lean_ctor_get(v_a_3958_, 0);
v_snd_3960_ = lean_ctor_get(v_a_3958_, 1);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_a_3958_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3962_ = v_a_3958_;
v_isShared_3963_ = v_isSharedCheck_4012_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_snd_3960_);
lean_inc(v_fst_3959_);
lean_dec(v_a_3958_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_4012_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v_a_3965_; lean_object* v___x_3966_; 
v___x_3964_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_fst_3959_, v___y_3953_);
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref(v___x_3964_);
v___x_3966_ = l_Lean_Expr_cleanupAnnotations(v_a_3965_);
if (lean_obj_tag(v___x_3966_) == 5)
{
lean_object* v_fn_3967_; lean_object* v_arg_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_del_object(v___x_3962_);
v_fn_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc_ref(v_fn_3967_);
v_arg_3968_ = lean_ctor_get(v___x_3966_, 1);
lean_inc_ref(v_arg_3968_);
lean_dec_ref_known(v___x_3966_, 2);
v___x_3969_ = lean_box(0);
v___x_3970_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fn_3967_, v___x_3969_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v_fst_3972_; lean_object* v_snd_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3997_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref_known(v___x_3970_, 1);
v_fst_3972_ = lean_ctor_get(v_a_3971_, 0);
v_snd_3973_ = lean_ctor_get(v_a_3971_, 1);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_a_3971_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3975_ = v_a_3971_;
v_isShared_3976_ = v_isSharedCheck_3997_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_snd_3973_);
lean_inc(v_fst_3972_);
lean_dec(v_a_3971_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3997_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3977_; 
lean_inc_ref(v_arg_3968_);
lean_inc(v_snd_3973_);
v___x_3977_ = l_Lean_Meta_mkCongrFun(v_snd_3973_, v_arg_3968_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref_known(v___x_3977_, 1);
v___x_3979_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_a_3947_, v_a_3978_, v___y_3953_);
lean_dec_ref(v___x_3979_);
v___x_3980_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0));
v___x_3981_ = l_Lean_Expr_app___override(v_fst_3972_, v_arg_3968_);
v___x_3982_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_3980_, v_snd_3960_, v___x_3981_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
lean_dec_ref_known(v___x_3982_, 1);
v___x_3983_ = l_Lean_Expr_mvarId_x21(v_snd_3973_);
lean_dec(v_snd_3973_);
v___x_3984_ = lean_box(0);
if (v_isShared_3976_ == 0)
{
lean_ctor_set_tag(v___x_3975_, 1);
lean_ctor_set(v___x_3975_, 1, v___x_3984_);
lean_ctor_set(v___x_3975_, 0, v___x_3983_);
v___x_3986_ = v___x_3975_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; 
v___x_3987_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3986_, v___y_3949_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3987_;
}
}
else
{
lean_del_object(v___x_3975_);
lean_dec(v_snd_3973_);
return v___x_3982_;
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_del_object(v___x_3975_);
lean_dec(v_snd_3973_);
lean_dec(v_fst_3972_);
lean_dec_ref(v_arg_3968_);
lean_dec(v_snd_3960_);
lean_dec(v_a_3947_);
v_a_3989_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3977_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3977_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec_ref(v_arg_3968_);
lean_dec(v_snd_3960_);
lean_dec(v_a_3947_);
v_a_3998_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3970_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3970_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
lean_dec(v_snd_3960_);
lean_dec(v_a_3947_);
v___x_4006_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2);
v___x_4007_ = l_Lean_indentExpr(v___x_3966_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set_tag(v___x_3962_, 7);
lean_ctor_set(v___x_3962_, 1, v___x_4007_);
lean_ctor_set(v___x_3962_, 0, v___x_4006_);
v___x_4009_ = v___x_3962_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v___x_4007_);
v___x_4009_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v___x_4009_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_4010_;
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v_a_3947_);
v_a_4013_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3957_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3957_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object* v_a_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(v_a_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4033_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___f_4043_; lean_object* v___x_4044_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_n(v_a_4042_, 2);
lean_dec_ref_known(v___x_4041_, 1);
v___f_4043_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4043_, 0, v_a_4042_);
v___x_4044_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_a_4042_, v___f_4043_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
return v___x_4044_;
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
v_a_4045_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4041_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4041_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object* v_x_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object* v_x_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Elab_Tactic_Conv_evalFun(v_x_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_x_4074_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object* v_mvarId_4085_, lean_object* v_val_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v___x_4096_; 
v___x_4096_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_4085_, v_val_4086_, v___y_4092_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object* v_mvarId_4097_, lean_object* v_val_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(v_mvarId_4097_, v_val_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object* v_00_u03b1_4109_, lean_object* v_msg_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; 
v___x_4120_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_4110_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
return v___x_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object* v_00_u03b1_4121_, lean_object* v_msg_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(v_00_u03b1_4121_, v_msg_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1(){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4147_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0));
v___x_4149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4150_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___boxed), 10, 0);
v___x_4151_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4147_, v___x_4148_, v___x_4149_, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object* v_a_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3(){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6));
v___x_4182_ = l_Lean_addBuiltinDeclarationRanges(v___x_4180_, v___x_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object* v_a_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
return v_res_4184_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0));
v___x_4187_ = l_Lean_stringToMessageData(v___x_4186_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object* v___x_4188_, lean_object* v_declName_4189_, lean_object* v_type_4190_, lean_object* v_value_4191_, lean_object* v_rhs_4192_, lean_object* v_a_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_inc_ref(v_a_4193_);
v___x_4199_ = l_Lean_Expr_app___override(v___x_4188_, v_a_4193_);
lean_inc(v___y_4197_);
lean_inc_ref(v___y_4196_);
lean_inc(v___y_4195_);
lean_inc_ref(v___y_4194_);
v___x_4200_ = lean_infer_type(v___x_4199_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; uint8_t v___x_4206_; uint8_t v___x_4207_; lean_object* v___x_4208_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc_n(v_a_4201_, 2);
lean_dec_ref_known(v___x_4200_, 1);
v___x_4202_ = lean_unsigned_to_nat(1u);
v___x_4203_ = lean_mk_empty_array_with_capacity(v___x_4202_);
v___x_4204_ = lean_array_push(v___x_4203_, v_a_4193_);
v___x_4205_ = 0;
v___x_4206_ = 1;
v___x_4207_ = 1;
v___x_4208_ = l_Lean_Meta_mkLambdaFVars(v___x_4204_, v_a_4201_, v___x_4205_, v___x_4206_, v___x_4205_, v___x_4206_, v___x_4207_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
lean_inc(v_a_4201_);
v___x_4210_ = l_Lean_Meta_getLevel(v_a_4201_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4210_, 1);
v___x_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4212_, 0, v_a_4201_);
v___x_4213_ = 0;
v___x_4214_ = lean_box(0);
v___x_4215_ = l_Lean_Meta_mkFreshExprMVar(v___x_4212_, v___x_4213_, v___x_4214_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4217_ = l_Lean_Meta_mkLambdaFVars(v___x_4204_, v_a_4216_, v___x_4205_, v___x_4206_, v___x_4205_, v___x_4206_, v___x_4207_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
lean_dec_ref(v___x_4204_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4251_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4220_ = v___x_4217_;
v_isShared_4221_ = v_isSharedCheck_4251_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4217_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4251_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4228_ = l_Lean_Expr_bindingBody_x21(v_a_4218_);
v___x_4229_ = l_Lean_Expr_letE___override(v_declName_4189_, v_type_4190_, v_value_4191_, v___x_4228_, v___x_4205_);
v___x_4230_ = l_Lean_Meta_isExprDefEq(v_rhs_4192_, v___x_4229_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; uint8_t v___x_4232_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v___x_4230_, 1);
v___x_4232_ = lean_unbox(v_a_4231_);
lean_dec(v_a_4231_);
if (v___x_4232_ == 0)
{
lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_del_object(v___x_4220_);
lean_dec(v_a_4218_);
lean_dec(v_a_4211_);
lean_dec(v_a_4209_);
v___x_4233_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1);
v___x_4234_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4233_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4234_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4234_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
else
{
goto v___jp_4222_;
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_del_object(v___x_4220_);
lean_dec(v_a_4218_);
lean_dec(v_a_4211_);
lean_dec(v_a_4209_);
v_a_4243_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4230_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4230_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
v___jp_4222_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4223_, 0, v_a_4211_);
lean_ctor_set(v___x_4223_, 1, v_a_4218_);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v_a_4209_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4224_);
v___x_4226_ = v___x_4220_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_a_4211_);
lean_dec(v_a_4209_);
lean_dec_ref(v_rhs_4192_);
lean_dec_ref(v_value_4191_);
lean_dec_ref(v_type_4190_);
lean_dec(v_declName_4189_);
v_a_4252_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4217_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4217_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec(v_a_4211_);
lean_dec(v_a_4209_);
lean_dec_ref(v___x_4204_);
lean_dec_ref(v_rhs_4192_);
lean_dec_ref(v_value_4191_);
lean_dec_ref(v_type_4190_);
lean_dec(v_declName_4189_);
v_a_4260_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4215_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4215_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
lean_dec(v_a_4209_);
lean_dec_ref(v___x_4204_);
lean_dec(v_a_4201_);
lean_dec_ref(v_rhs_4192_);
lean_dec_ref(v_value_4191_);
lean_dec_ref(v_type_4190_);
lean_dec(v_declName_4189_);
v_a_4268_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4210_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4210_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec_ref(v___x_4204_);
lean_dec(v_a_4201_);
lean_dec_ref(v_rhs_4192_);
lean_dec_ref(v_value_4191_);
lean_dec_ref(v_type_4190_);
lean_dec(v_declName_4189_);
v_a_4276_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4208_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4208_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref(v_a_4193_);
lean_dec_ref(v_rhs_4192_);
lean_dec_ref(v_value_4191_);
lean_dec_ref(v_type_4190_);
lean_dec(v_declName_4189_);
v_a_4284_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4200_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4200_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object* v___x_4292_, lean_object* v_declName_4293_, lean_object* v_type_4294_, lean_object* v_value_4295_, lean_object* v_rhs_4296_, lean_object* v_a_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(v___x_4292_, v_declName_4293_, v_type_4294_, v_value_4295_, v_rhs_4296_, v_a_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object* v___x_4304_, lean_object* v_snd_4305_, lean_object* v_x_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4312_ = lean_unsigned_to_nat(1u);
v___x_4313_ = lean_mk_empty_array_with_capacity(v___x_4312_);
v___x_4314_ = lean_array_push(v___x_4313_, v_x_4306_);
lean_inc_ref_n(v___x_4314_, 2);
v___x_4315_ = l_Lean_Expr_beta(v___x_4304_, v___x_4314_);
v___x_4316_ = l_Lean_Expr_beta(v_snd_4305_, v___x_4314_);
v___x_4317_ = l_Lean_Meta_mkEq(v___x_4315_, v___x_4316_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4319_ = lean_box(0);
v___x_4320_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4318_, v___x_4319_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; uint8_t v___x_4322_; uint8_t v___x_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc_n(v_a_4321_, 2);
lean_dec_ref_known(v___x_4320_, 1);
v___x_4322_ = 0;
v___x_4323_ = 1;
v___x_4324_ = 1;
v___x_4325_ = l_Lean_Meta_mkLambdaFVars(v___x_4314_, v_a_4321_, v___x_4322_, v___x_4323_, v___x_4322_, v___x_4323_, v___x_4324_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec_ref(v___x_4314_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4335_; 
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4335_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4335_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4333_; 
v___x_4330_ = l_Lean_Expr_mvarId_x21(v_a_4321_);
lean_dec(v_a_4321_);
v___x_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4331_, 0, v_a_4326_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 0, v___x_4331_);
v___x_4333_ = v___x_4328_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4331_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v_a_4321_);
v_a_4336_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4325_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4325_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec_ref(v___x_4314_);
v_a_4344_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4320_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4320_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec_ref(v___x_4314_);
v_a_4352_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4317_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4317_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object* v___x_4360_, lean_object* v_snd_4361_, lean_object* v_x_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(v___x_4360_, v_snd_4361_, v_x_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
return v_res_4368_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2));
v___x_4374_ = l_Lean_stringToMessageData(v___x_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object* v_mvarId_4375_, lean_object* v_lhs_4376_, lean_object* v_rhs_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_){
_start:
{
if (lean_obj_tag(v_lhs_4376_) == 8)
{
lean_object* v_declName_4383_; lean_object* v_type_4384_; lean_object* v_value_4385_; lean_object* v_body_4386_; lean_object* v___x_4387_; 
v_declName_4383_ = lean_ctor_get(v_lhs_4376_, 0);
lean_inc(v_declName_4383_);
v_type_4384_ = lean_ctor_get(v_lhs_4376_, 1);
lean_inc_ref_n(v_type_4384_, 2);
v_value_4385_ = lean_ctor_get(v_lhs_4376_, 2);
lean_inc_ref(v_value_4385_);
v_body_4386_ = lean_ctor_get(v_lhs_4376_, 3);
lean_inc_ref(v_body_4386_);
lean_dec_ref_known(v_lhs_4376_, 4);
v___x_4387_ = l_Lean_Meta_getLevel(v_type_4384_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; uint8_t v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v___x_4389_ = 0;
lean_inc_ref(v_type_4384_);
lean_inc(v_declName_4383_);
v___x_4390_ = l_Lean_mkLambda(v_declName_4383_, v___x_4389_, v_type_4384_, v_body_4386_);
lean_inc_ref(v___x_4390_);
v___x_4391_ = l_Lean_Meta_isTypeCorrect(v___x_4390_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___f_4393_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4398_; uint8_t v___x_4470_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
lean_inc_ref(v_value_4385_);
lean_inc_ref(v_type_4384_);
lean_inc(v_declName_4383_);
lean_inc_ref(v___x_4390_);
v___f_4393_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4393_, 0, v___x_4390_);
lean_closure_set(v___f_4393_, 1, v_declName_4383_);
lean_closure_set(v___f_4393_, 2, v_type_4384_);
lean_closure_set(v___f_4393_, 3, v_value_4385_);
lean_closure_set(v___f_4393_, 4, v_rhs_4377_);
v___x_4470_ = lean_unbox(v_a_4392_);
lean_dec(v_a_4392_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec_ref(v___f_4393_);
lean_dec_ref(v___x_4390_);
lean_dec(v_a_4388_);
lean_dec_ref(v_value_4385_);
lean_dec_ref(v_type_4384_);
lean_dec(v_declName_4383_);
lean_dec(v_mvarId_4375_);
v___x_4471_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3);
v___x_4472_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4471_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4472_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
else
{
v___y_4395_ = v_a_4378_;
v___y_4396_ = v_a_4379_;
v___y_4397_ = v_a_4380_;
v___y_4398_ = v_a_4381_;
goto v___jp_4394_;
}
v___jp_4394_:
{
lean_object* v___x_4399_; 
lean_inc_ref(v_type_4384_);
lean_inc(v_declName_4383_);
v___x_4399_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4383_, v_type_4384_, v___f_4393_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v_snd_4401_; lean_object* v_fst_4402_; lean_object* v_fst_4403_; lean_object* v_snd_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4461_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v_snd_4401_ = lean_ctor_get(v_a_4400_, 1);
lean_inc(v_snd_4401_);
v_fst_4402_ = lean_ctor_get(v_a_4400_, 0);
lean_inc(v_fst_4402_);
lean_dec(v_a_4400_);
v_fst_4403_ = lean_ctor_get(v_snd_4401_, 0);
v_snd_4404_ = lean_ctor_get(v_snd_4401_, 1);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_snd_4401_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4406_ = v_snd_4401_;
v_isShared_4407_ = v_isSharedCheck_4461_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_snd_4404_);
lean_inc(v_fst_4403_);
lean_dec(v_snd_4401_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4461_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___f_4408_; lean_object* v___x_4409_; 
lean_inc(v_snd_4404_);
lean_inc_ref(v___x_4390_);
v___f_4408_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4408_, 0, v___x_4390_);
lean_closure_set(v___f_4408_, 1, v_snd_4404_);
lean_inc_ref(v_type_4384_);
v___x_4409_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4383_, v_type_4384_, v___f_4408_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v_fst_4411_; lean_object* v_snd_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4452_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v_fst_4411_ = lean_ctor_get(v_a_4410_, 0);
v_snd_4412_ = lean_ctor_get(v_a_4410_, 1);
v_isSharedCheck_4452_ = !lean_is_exclusive(v_a_4410_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4414_ = v_a_4410_;
v_isShared_4415_ = v_isSharedCheck_4452_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_snd_4412_);
lean_inc(v_fst_4411_);
lean_dec(v_a_4410_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4452_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4419_; 
v___x_4416_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1));
v___x_4417_ = lean_box(0);
if (v_isShared_4415_ == 0)
{
lean_ctor_set_tag(v___x_4414_, 1);
lean_ctor_set(v___x_4414_, 1, v___x_4417_);
lean_ctor_set(v___x_4414_, 0, v_fst_4403_);
v___x_4419_ = v___x_4414_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_fst_4403_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_object* v___x_4421_; 
if (v_isShared_4407_ == 0)
{
lean_ctor_set_tag(v___x_4406_, 1);
lean_ctor_set(v___x_4406_, 1, v___x_4419_);
lean_ctor_set(v___x_4406_, 0, v_a_4388_);
v___x_4421_ = v___x_4406_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4388_);
lean_ctor_set(v_reuseFailAlloc_4450_, 1, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4448_; 
v___x_4422_ = l_Lean_mkConst(v___x_4416_, v___x_4421_);
v___x_4423_ = l_Lean_mkApp6(v___x_4422_, v_type_4384_, v_fst_4402_, v___x_4390_, v_snd_4404_, v_value_4385_, v_fst_4411_);
v___x_4424_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4375_, v___x_4423_, v___y_4396_);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4448_ == 0)
{
lean_object* v_unused_4449_; 
v_unused_4449_ = lean_ctor_get(v___x_4424_, 0);
lean_dec(v_unused_4449_);
v___x_4426_ = v___x_4424_;
v_isShared_4427_ = v_isSharedCheck_4448_;
goto v_resetjp_4425_;
}
else
{
lean_dec(v___x_4424_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4448_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4428_; 
v___x_4428_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4412_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4439_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4431_ = v___x_4428_;
v_isShared_4432_ = v_isSharedCheck_4439_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_a_4429_);
lean_dec(v___x_4428_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4439_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4427_ == 0)
{
lean_ctor_set_tag(v___x_4426_, 1);
lean_ctor_set(v___x_4426_, 0, v_a_4429_);
v___x_4434_ = v___x_4426_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4429_);
v___x_4434_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
lean_object* v___x_4436_; 
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v___x_4434_);
v___x_4436_ = v___x_4431_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4447_; 
lean_del_object(v___x_4426_);
v_a_4440_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4442_ = v___x_4428_;
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v___x_4428_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4447_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
if (v_isShared_4443_ == 0)
{
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
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
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4406_);
lean_dec(v_snd_4404_);
lean_dec(v_fst_4403_);
lean_dec(v_fst_4402_);
lean_dec_ref(v___x_4390_);
lean_dec(v_a_4388_);
lean_dec_ref(v_value_4385_);
lean_dec_ref(v_type_4384_);
lean_dec(v_mvarId_4375_);
v_a_4453_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4409_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4409_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec_ref(v___x_4390_);
lean_dec(v_a_4388_);
lean_dec_ref(v_value_4385_);
lean_dec_ref(v_type_4384_);
lean_dec(v_declName_4383_);
lean_dec(v_mvarId_4375_);
v_a_4462_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4399_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4399_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec_ref(v___x_4390_);
lean_dec(v_a_4388_);
lean_dec_ref(v_value_4385_);
lean_dec_ref(v_type_4384_);
lean_dec(v_declName_4383_);
lean_dec_ref(v_rhs_4377_);
lean_dec(v_mvarId_4375_);
v_a_4481_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4391_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4391_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec_ref(v_body_4386_);
lean_dec_ref(v_value_4385_);
lean_dec_ref(v_type_4384_);
lean_dec(v_declName_4383_);
lean_dec_ref(v_rhs_4377_);
lean_dec(v_mvarId_4375_);
v_a_4489_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4387_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4387_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
else
{
lean_object* v___x_4497_; lean_object* v___x_4498_; 
lean_dec_ref(v_rhs_4377_);
lean_dec_ref(v_lhs_4376_);
lean_dec(v_mvarId_4375_);
v___x_4497_ = lean_box(0);
v___x_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
return v___x_4498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object* v_mvarId_4499_, lean_object* v_lhs_4500_, lean_object* v_rhs_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v_res_4507_; 
v_res_4507_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4499_, v_lhs_4500_, v_rhs_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec(v_a_4505_);
lean_dec_ref(v_a_4504_);
lean_dec(v_a_4503_);
lean_dec_ref(v_a_4502_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object* v_body_4509_, lean_object* v_snd_4510_, lean_object* v_b_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v___x_4517_ = lean_expr_instantiate1(v_body_4509_, v_b_4511_);
v___x_4518_ = lean_box(0);
v___x_4519_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_4517_, v___x_4518_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v_fst_4521_; lean_object* v_snd_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4584_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
v_fst_4521_ = lean_ctor_get(v_a_4520_, 0);
v_snd_4522_ = lean_ctor_get(v_a_4520_, 1);
v_isSharedCheck_4584_ = !lean_is_exclusive(v_a_4520_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4524_ = v_a_4520_;
v_isShared_4525_ = v_isSharedCheck_4584_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_snd_4522_);
lean_inc(v_fst_4521_);
lean_dec(v_a_4520_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4584_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; uint8_t v___x_4530_; uint8_t v___x_4531_; lean_object* v___x_4532_; 
v___x_4526_ = lean_unsigned_to_nat(1u);
v___x_4527_ = lean_mk_empty_array_with_capacity(v___x_4526_);
v___x_4528_ = lean_array_push(v___x_4527_, v_b_4511_);
v___x_4529_ = 0;
v___x_4530_ = 1;
v___x_4531_ = 1;
lean_inc(v_fst_4521_);
v___x_4532_ = l_Lean_Meta_mkLambdaFVars(v___x_4528_, v_fst_4521_, v___x_4529_, v___x_4530_, v___x_4529_, v___x_4530_, v___x_4531_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4534_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc(v_a_4533_);
lean_dec_ref_known(v___x_4532_, 1);
lean_inc(v_snd_4522_);
v___x_4534_ = l_Lean_Meta_mkLambdaFVars(v___x_4528_, v_snd_4522_, v___x_4529_, v___x_4530_, v___x_4529_, v___x_4530_, v___x_4531_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; lean_object* v___x_4536_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref_known(v___x_4534_, 1);
v___x_4536_ = l_Lean_Meta_mkForallFVars(v___x_4528_, v_fst_4521_, v___x_4529_, v___x_4530_, v___x_4530_, v___x_4531_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
lean_dec_ref(v___x_4528_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_4539_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_4538_, v_snd_4510_, v_a_4537_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4550_; 
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; 
v_unused_4551_ = lean_ctor_get(v___x_4539_, 0);
lean_dec(v_unused_4551_);
v___x_4541_ = v___x_4539_;
v_isShared_4542_ = v_isSharedCheck_4550_;
goto v_resetjp_4540_;
}
else
{
lean_dec(v___x_4539_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4550_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v_a_4535_);
v___x_4544_ = v___x_4524_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4535_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_snd_4522_);
v___x_4544_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4545_; lean_object* v___x_4547_; 
v___x_4545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4545_, 0, v_a_4533_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v___x_4545_);
v___x_4547_ = v___x_4541_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_a_4535_);
lean_dec(v_a_4533_);
lean_del_object(v___x_4524_);
lean_dec(v_snd_4522_);
v_a_4552_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4539_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4539_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
else
{
lean_object* v_a_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4567_; 
lean_dec(v_a_4535_);
lean_dec(v_a_4533_);
lean_del_object(v___x_4524_);
lean_dec(v_snd_4522_);
lean_dec_ref(v_snd_4510_);
v_a_4560_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4562_ = v___x_4536_;
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_a_4560_);
lean_dec(v___x_4536_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4567_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4565_; 
if (v_isShared_4563_ == 0)
{
v___x_4565_ = v___x_4562_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v_a_4560_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec(v_a_4533_);
lean_dec_ref(v___x_4528_);
lean_del_object(v___x_4524_);
lean_dec(v_snd_4522_);
lean_dec(v_fst_4521_);
lean_dec_ref(v_snd_4510_);
v_a_4568_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4534_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4534_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
lean_dec_ref(v___x_4528_);
lean_del_object(v___x_4524_);
lean_dec(v_snd_4522_);
lean_dec(v_fst_4521_);
lean_dec_ref(v_snd_4510_);
v_a_4576_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4532_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4532_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec_ref(v_b_4511_);
lean_dec_ref(v_snd_4510_);
v_a_4585_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4519_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4519_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object* v_body_4593_, lean_object* v_snd_4594_, lean_object* v_b_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(v_body_4593_, v_snd_4594_, v_b_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
lean_dec(v___y_4599_);
lean_dec_ref(v___y_4598_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec_ref(v_body_4593_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object* v_body_4602_, lean_object* v_snd_4603_, lean_object* v_name_4604_, uint8_t v_bi_4605_, lean_object* v_type_4606_, uint8_t v_kind_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___f_4613_; lean_object* v___x_4614_; 
v___f_4613_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4613_, 0, v_body_4602_);
lean_closure_set(v___f_4613_, 1, v_snd_4603_);
v___x_4614_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4604_, v_bi_4605_, v_type_4606_, v___f_4613_, v_kind_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
v_a_4623_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4614_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4614_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object* v_body_4631_, lean_object* v_snd_4632_, lean_object* v_name_4633_, lean_object* v_bi_4634_, lean_object* v_type_4635_, lean_object* v_kind_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
uint8_t v_bi_boxed_4642_; uint8_t v_kind_boxed_4643_; lean_object* v_res_4644_; 
v_bi_boxed_4642_ = lean_unbox(v_bi_4634_);
v_kind_boxed_4643_ = lean_unbox(v_kind_4636_);
v_res_4644_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4631_, v_snd_4632_, v_name_4633_, v_bi_boxed_4642_, v_type_4635_, v_kind_boxed_4643_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
return v_res_4644_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0));
v___x_4647_ = l_Lean_stringToMessageData(v___x_4646_);
return v___x_4647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6));
v___x_4656_ = l_Lean_stringToMessageData(v___x_4655_);
return v___x_4656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8));
v___x_4659_ = l_Lean_stringToMessageData(v___x_4658_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object* v_mvarId_4660_, lean_object* v_userName_x3f_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v___y_4668_; uint8_t v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___x_4738_; 
lean_inc(v_mvarId_4660_);
v___x_4738_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_4660_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v_a_4739_; lean_object* v_fst_4740_; lean_object* v_snd_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4874_; 
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
lean_inc(v_a_4739_);
lean_dec_ref_known(v___x_4738_, 1);
v_fst_4740_ = lean_ctor_get(v_a_4739_, 0);
v_snd_4741_ = lean_ctor_get(v_a_4739_, 1);
v_isSharedCheck_4874_ = !lean_is_exclusive(v_a_4739_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4743_ = v_a_4739_;
v_isShared_4744_ = v_isSharedCheck_4874_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_snd_4741_);
lean_inc(v_fst_4740_);
lean_dec(v_a_4739_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4874_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4745_; lean_object* v_a_4746_; lean_object* v___x_4747_; 
v___x_4745_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_4740_, v___y_4663_);
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4746_);
lean_dec_ref(v___x_4745_);
v___x_4747_ = l_Lean_Expr_cleanupAnnotations(v_a_4746_);
if (lean_obj_tag(v___x_4747_) == 7)
{
lean_object* v_binderName_4748_; lean_object* v_binderType_4749_; lean_object* v_body_4750_; uint8_t v_binderInfo_4751_; lean_object* v___x_4752_; 
lean_del_object(v___x_4743_);
v_binderName_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_binderName_4748_);
v_binderType_4749_ = lean_ctor_get(v___x_4747_, 1);
lean_inc_ref_n(v_binderType_4749_, 2);
v_body_4750_ = lean_ctor_get(v___x_4747_, 2);
lean_inc_ref(v_body_4750_);
v_binderInfo_4751_ = lean_ctor_get_uint8(v___x_4747_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_4747_, 3);
v___x_4752_ = l_Lean_Meta_getLevel(v_binderType_4749_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v_a_4753_; lean_object* v___x_4754_; lean_object* v_userName_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; 
v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
lean_inc(v_a_4753_);
lean_dec_ref_known(v___x_4752_, 1);
lean_inc_ref(v_body_4750_);
lean_inc_ref(v_binderType_4749_);
lean_inc(v_binderName_4748_);
v___x_4754_ = l_Lean_Expr_lam___override(v_binderName_4748_, v_binderType_4749_, v_body_4750_, v_binderInfo_4751_);
if (lean_obj_tag(v_userName_x3f_4661_) == 1)
{
lean_object* v_val_4797_; 
lean_dec(v_binderName_4748_);
v_val_4797_ = lean_ctor_get(v_userName_x3f_4661_, 0);
lean_inc(v_val_4797_);
lean_dec_ref_known(v_userName_x3f_4661_, 1);
v_userName_4756_ = v_val_4797_;
v___y_4757_ = v___y_4662_;
v___y_4758_ = v___y_4663_;
v___y_4759_ = v___y_4664_;
v___y_4760_ = v___y_4665_;
goto v___jp_4755_;
}
else
{
lean_object* v___x_4798_; 
lean_dec(v_userName_x3f_4661_);
v___x_4798_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_4748_, v___y_4662_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
v_userName_4756_ = v_a_4799_;
v___y_4757_ = v___y_4662_;
v___y_4758_ = v___y_4663_;
v___y_4759_ = v___y_4664_;
v___y_4760_ = v___y_4665_;
goto v___jp_4755_;
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_dec_ref(v___x_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_body_4750_);
lean_dec_ref(v_binderType_4749_);
lean_dec(v_snd_4741_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_mvarId_4660_);
v_a_4800_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4798_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4798_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
v___jp_4755_:
{
uint8_t v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = 0;
lean_inc_ref(v_binderType_4749_);
v___x_4762_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4750_, v_snd_4741_, v_userName_4756_, v_binderInfo_4751_, v_binderType_4749_, v___x_4761_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec_ref(v___y_4757_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_object* v_a_4763_; lean_object* v_snd_4764_; lean_object* v_fst_4765_; lean_object* v_fst_4766_; lean_object* v_snd_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4788_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref_known(v___x_4762_, 1);
v_snd_4764_ = lean_ctor_get(v_a_4763_, 1);
lean_inc(v_snd_4764_);
v_fst_4765_ = lean_ctor_get(v_a_4763_, 0);
lean_inc(v_fst_4765_);
lean_dec(v_a_4763_);
v_fst_4766_ = lean_ctor_get(v_snd_4764_, 0);
v_snd_4767_ = lean_ctor_get(v_snd_4764_, 1);
v_isSharedCheck_4788_ = !lean_is_exclusive(v_snd_4764_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4769_ = v_snd_4764_;
v_isShared_4770_ = v_isSharedCheck_4788_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_snd_4767_);
lean_inc(v_fst_4766_);
lean_dec(v_snd_4764_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4788_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
v___x_4771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5));
v___x_4772_ = lean_box(0);
if (v_isShared_4770_ == 0)
{
lean_ctor_set_tag(v___x_4769_, 1);
lean_ctor_set(v___x_4769_, 1, v___x_4772_);
lean_ctor_set(v___x_4769_, 0, v_a_4753_);
v___x_4774_ = v___x_4769_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4753_);
lean_ctor_set(v_reuseFailAlloc_4787_, 1, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4785_; 
v___x_4775_ = l_Lean_mkConst(v___x_4771_, v___x_4774_);
v___x_4776_ = l_Lean_mkApp4(v___x_4775_, v_binderType_4749_, v___x_4754_, v_fst_4765_, v_fst_4766_);
v___x_4777_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4660_, v___x_4776_, v___y_4758_);
lean_dec(v___y_4758_);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4785_ == 0)
{
lean_object* v_unused_4786_; 
v_unused_4786_ = lean_ctor_get(v___x_4777_, 0);
lean_dec(v_unused_4786_);
v___x_4779_ = v___x_4777_;
v_isShared_4780_ = v_isSharedCheck_4785_;
goto v_resetjp_4778_;
}
else
{
lean_dec(v___x_4777_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4785_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4781_; lean_object* v___x_4783_; 
v___x_4781_ = l_Lean_Expr_mvarId_x21(v_snd_4767_);
lean_dec(v_snd_4767_);
if (v_isShared_4780_ == 0)
{
lean_ctor_set(v___x_4779_, 0, v___x_4781_);
v___x_4783_ = v___x_4779_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
}
else
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4796_; 
lean_dec(v___y_4758_);
lean_dec_ref(v___x_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_binderType_4749_);
lean_dec(v_mvarId_4660_);
v_a_4789_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4791_ = v___x_4762_;
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4762_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4796_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4794_; 
if (v_isShared_4792_ == 0)
{
v___x_4794_ = v___x_4791_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_a_4789_);
v___x_4794_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
return v___x_4794_;
}
}
}
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec_ref(v_body_4750_);
lean_dec_ref(v_binderType_4749_);
lean_dec(v_binderName_4748_);
lean_dec(v_snd_4741_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v_a_4808_ = lean_ctor_get(v___x_4752_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4752_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4752_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
else
{
lean_object* v___x_4816_; 
lean_inc_ref(v___x_4747_);
lean_inc(v_mvarId_4660_);
v___x_4816_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4660_, v___x_4747_, v_snd_4741_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4865_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4819_ = v___x_4816_;
v_isShared_4820_ = v_isSharedCheck_4865_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4816_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4865_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
if (lean_obj_tag(v_a_4817_) == 1)
{
lean_object* v_val_4821_; lean_object* v___x_4823_; 
lean_dec_ref(v___x_4747_);
lean_del_object(v___x_4743_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v_val_4821_ = lean_ctor_get(v_a_4817_, 0);
lean_inc(v_val_4821_);
lean_dec_ref_known(v_a_4817_, 1);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v_val_4821_);
v___x_4823_ = v___x_4819_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_val_4821_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
else
{
lean_object* v___x_4825_; 
lean_del_object(v___x_4819_);
lean_dec(v_a_4817_);
lean_inc(v___y_4665_);
lean_inc_ref(v___y_4664_);
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc_ref(v___x_4747_);
v___x_4825_ = lean_infer_type(v___x_4747_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v_a_4826_; lean_object* v___x_4827_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref_known(v___x_4825_, 1);
v___x_4827_ = l_Lean_Meta_whnfD(v_a_4826_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; uint8_t v___x_4829_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_a_4828_);
lean_dec_ref_known(v___x_4827_, 1);
v___x_4829_ = l_Lean_Expr_isForall(v_a_4828_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4834_; 
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v___x_4830_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7);
v___x_4831_ = l_Lean_MessageData_ofExpr(v___x_4747_);
v___x_4832_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9);
if (v_isShared_4744_ == 0)
{
lean_ctor_set_tag(v___x_4743_, 7);
lean_ctor_set(v___x_4743_, 1, v___x_4832_);
lean_ctor_set(v___x_4743_, 0, v___x_4831_);
v___x_4834_ = v___x_4743_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4831_);
lean_ctor_set(v_reuseFailAlloc_4848_, 1, v___x_4832_);
v___x_4834_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
v___x_4835_ = l_Lean_MessageData_ofExpr(v_a_4828_);
v___x_4836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4834_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
v___x_4837_ = l_Lean_indentD(v___x_4836_);
v___x_4838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4830_);
lean_ctor_set(v___x_4838_, 1, v___x_4837_);
v___x_4839_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4838_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4839_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4839_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
else
{
lean_dec(v_a_4828_);
lean_dec_ref(v___x_4747_);
lean_del_object(v___x_4743_);
v___y_4696_ = v___y_4662_;
v___y_4697_ = v___y_4663_;
v___y_4698_ = v___y_4664_;
v___y_4699_ = v___y_4665_;
goto v___jp_4695_;
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_dec_ref(v___x_4747_);
lean_del_object(v___x_4743_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v_a_4849_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4827_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4827_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
lean_object* v___x_4854_; 
if (v_isShared_4852_ == 0)
{
v___x_4854_ = v___x_4851_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec_ref(v___x_4747_);
lean_del_object(v___x_4743_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v_a_4857_ = lean_ctor_get(v___x_4825_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4825_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4825_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4825_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
}
else
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4873_; 
lean_dec_ref(v___x_4747_);
lean_del_object(v___x_4743_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v_a_4866_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4816_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4816_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
lean_object* v___x_4871_; 
if (v_isShared_4869_ == 0)
{
v___x_4871_ = v___x_4868_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
}
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v_a_4875_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4877_ = v___x_4738_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4738_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
v___jp_4667_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = lean_unsigned_to_nat(1u);
v___x_4676_ = l_Lean_Meta_introNCore(v___y_4673_, v___x_4675_, v___y_4674_, v___y_4669_, v___y_4669_, v___y_4671_, v___y_4668_, v___y_4670_, v___y_4672_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v_snd_4678_; lean_object* v___x_4679_; 
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
lean_inc(v_a_4677_);
lean_dec_ref_known(v___x_4676_, 1);
v_snd_4678_ = lean_ctor_get(v_a_4677_, 1);
lean_inc(v_snd_4678_);
lean_dec(v_a_4677_);
v___x_4679_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4678_, v___y_4671_, v___y_4668_, v___y_4670_, v___y_4672_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4671_);
return v___x_4679_;
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4687_; 
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4668_);
v_a_4680_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4682_ = v___x_4676_;
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4676_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
v___jp_4688_:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; 
v___x_4693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1);
v___x_4694_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4693_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
return v___x_4694_;
}
v___jp_4695_:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3));
v___x_4701_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_4700_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; uint8_t v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
v___x_4703_ = 0;
v___x_4704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2));
v___x_4705_ = lean_box(0);
v___x_4706_ = l_Lean_MVarId_apply(v_mvarId_4660_, v_a_4702_, v___x_4704_, v___x_4705_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4706_, 1);
if (lean_obj_tag(v_a_4707_) == 1)
{
lean_object* v_tail_4708_; 
v_tail_4708_ = lean_ctor_get(v_a_4707_, 1);
if (lean_obj_tag(v_tail_4708_) == 0)
{
if (lean_obj_tag(v_userName_x3f_4661_) == 1)
{
lean_object* v_head_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4718_; 
v_head_4709_ = lean_ctor_get(v_a_4707_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v_a_4707_);
if (v_isSharedCheck_4718_ == 0)
{
lean_object* v_unused_4719_; 
v_unused_4719_ = lean_ctor_get(v_a_4707_, 1);
lean_dec(v_unused_4719_);
v___x_4711_ = v_a_4707_;
v_isShared_4712_ = v_isSharedCheck_4718_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_head_4709_);
lean_dec(v_a_4707_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4718_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v_val_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
v_val_4713_ = lean_ctor_get(v_userName_x3f_4661_, 0);
lean_inc(v_val_4713_);
lean_dec_ref_known(v_userName_x3f_4661_, 1);
v___x_4714_ = lean_box(0);
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 1, v___x_4714_);
lean_ctor_set(v___x_4711_, 0, v_val_4713_);
v___x_4716_ = v___x_4711_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_val_4713_);
lean_ctor_set(v_reuseFailAlloc_4717_, 1, v___x_4714_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
v___y_4668_ = v___y_4697_;
v___y_4669_ = v___x_4703_;
v___y_4670_ = v___y_4698_;
v___y_4671_ = v___y_4696_;
v___y_4672_ = v___y_4699_;
v___y_4673_ = v_head_4709_;
v___y_4674_ = v___x_4716_;
goto v___jp_4667_;
}
}
}
else
{
lean_object* v_head_4720_; lean_object* v___x_4721_; 
lean_dec(v_userName_x3f_4661_);
v_head_4720_ = lean_ctor_get(v_a_4707_, 0);
lean_inc(v_head_4720_);
lean_dec_ref_known(v_a_4707_, 2);
v___x_4721_ = lean_box(0);
v___y_4668_ = v___y_4697_;
v___y_4669_ = v___x_4703_;
v___y_4670_ = v___y_4698_;
v___y_4671_ = v___y_4696_;
v___y_4672_ = v___y_4699_;
v___y_4673_ = v_head_4720_;
v___y_4674_ = v___x_4721_;
goto v___jp_4667_;
}
}
else
{
lean_dec_ref_known(v_a_4707_, 2);
lean_dec(v_userName_x3f_4661_);
v___y_4689_ = v___y_4696_;
v___y_4690_ = v___y_4697_;
v___y_4691_ = v___y_4698_;
v___y_4692_ = v___y_4699_;
goto v___jp_4688_;
}
}
else
{
lean_dec(v_a_4707_);
lean_dec(v_userName_x3f_4661_);
v___y_4689_ = v___y_4696_;
v___y_4690_ = v___y_4697_;
v___y_4691_ = v___y_4698_;
v___y_4692_ = v___y_4699_;
goto v___jp_4688_;
}
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v_userName_x3f_4661_);
v_a_4722_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4706_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4706_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v_userName_x3f_4661_);
lean_dec(v_mvarId_4660_);
v_a_4730_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4701_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4701_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed(lean_object* v_mvarId_4883_, lean_object* v_userName_x3f_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(v_mvarId_4883_, v_userName_x3f_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(lean_object* v_mvarId_4891_, lean_object* v_userName_x3f_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_){
_start:
{
lean_object* v___f_4898_; lean_object* v___x_4899_; 
lean_inc(v_mvarId_4891_);
v___f_4898_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4898_, 0, v_mvarId_4891_);
lean_closure_set(v___f_4898_, 1, v_userName_x3f_4892_);
v___x_4899_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_4891_, v___f_4898_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___boxed(lean_object* v_mvarId_4900_, lean_object* v_userName_x3f_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_mvarId_4900_, v_userName_x3f_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(lean_object* v_userName_x3f_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4917_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
lean_inc(v_a_4916_);
lean_dec_ref_known(v___x_4915_, 1);
v___x_4917_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_a_4916_, v_userName_x3f_4908_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref_known(v___x_4917_, 1);
v___x_4919_ = lean_box(0);
v___x_4920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4920_, 0, v_a_4918_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
v___x_4921_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4920_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
return v___x_4921_;
}
else
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
v_a_4922_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4929_ == 0)
{
v___x_4924_ = v___x_4917_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4917_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
else
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4937_; 
lean_dec(v_userName_x3f_4908_);
v_a_4930_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4937_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4937_ == 0)
{
v___x_4932_ = v___x_4915_;
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4915_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4937_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4936_; 
v_reuseFailAlloc_4936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4936_, 0, v_a_4930_);
v___x_4935_ = v_reuseFailAlloc_4936_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
return v___x_4935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg___boxed(lean_object* v_userName_x3f_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v_a_4939_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(lean_object* v_userName_x3f_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_4946_, v_a_4948_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_);
return v___x_4956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___boxed(lean_object* v_userName_x3f_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(v_userName_x3f_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_);
lean_dec(v_a_4965_);
lean_dec_ref(v_a_4964_);
lean_dec(v_a_4963_);
lean_dec_ref(v_a_4962_);
lean_dec(v_a_4961_);
lean_dec_ref(v_a_4960_);
lean_dec(v_a_4959_);
lean_dec_ref(v_a_4958_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(lean_object* v_as_4975_, size_t v_sz_4976_, size_t v_i_4977_, lean_object* v_b_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
uint8_t v___x_4985_; 
v___x_4985_ = lean_usize_dec_lt(v_i_4977_, v_sz_4976_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
v___x_4986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4986_, 0, v_b_4978_);
return v___x_4986_;
}
else
{
lean_object* v___x_4987_; lean_object* v_a_4988_; lean_object* v___y_4990_; lean_object* v___x_5002_; uint8_t v___x_5003_; 
v___x_4987_ = lean_box(0);
v_a_4988_ = lean_array_uget_borrowed(v_as_4975_, v_i_4977_);
v___x_5002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1));
lean_inc(v_a_4988_);
v___x_5003_ = l_Lean_Syntax_isOfKind(v_a_4988_, v___x_5002_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; 
v___x_5004_ = lean_box(0);
v___y_4990_ = v___x_5004_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; uint8_t v___x_5008_; 
v___x_5005_ = lean_unsigned_to_nat(0u);
v___x_5006_ = l_Lean_Syntax_getArg(v_a_4988_, v___x_5005_);
v___x_5007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3));
lean_inc(v___x_5006_);
v___x_5008_ = l_Lean_Syntax_isOfKind(v___x_5006_, v___x_5007_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; 
lean_dec(v___x_5006_);
v___x_5009_ = lean_box(0);
v___y_4990_ = v___x_5009_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5010_ = l_Lean_TSyntax_getId(v___x_5006_);
lean_dec(v___x_5006_);
v___x_5011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5010_);
v___y_4990_ = v___x_5011_;
goto v___jp_4989_;
}
}
v___jp_4989_:
{
lean_object* v_toCold_4991_; lean_object* v_currRecDepth_4992_; lean_object* v_ref_4993_; uint8_t v_diag_4994_; uint8_t v_suppressElabErrors_4995_; lean_object* v_ref_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v_toCold_4991_ = lean_ctor_get(v___y_4982_, 0);
v_currRecDepth_4992_ = lean_ctor_get(v___y_4982_, 1);
v_ref_4993_ = lean_ctor_get(v___y_4982_, 2);
v_diag_4994_ = lean_ctor_get_uint8(v___y_4982_, sizeof(void*)*3);
v_suppressElabErrors_4995_ = lean_ctor_get_uint8(v___y_4982_, sizeof(void*)*3 + 1);
v_ref_4996_ = l_Lean_replaceRef(v_a_4988_, v_ref_4993_);
lean_inc(v_currRecDepth_4992_);
lean_inc_ref(v_toCold_4991_);
v___x_4997_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4997_, 0, v_toCold_4991_);
lean_ctor_set(v___x_4997_, 1, v_currRecDepth_4992_);
lean_ctor_set(v___x_4997_, 2, v_ref_4996_);
lean_ctor_set_uint8(v___x_4997_, sizeof(void*)*3, v_diag_4994_);
lean_ctor_set_uint8(v___x_4997_, sizeof(void*)*3 + 1, v_suppressElabErrors_4995_);
v___x_4998_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___y_4990_, v___y_4979_, v___y_4980_, v___y_4981_, v___x_4997_, v___y_4983_);
lean_dec_ref_known(v___x_4997_, 3);
if (lean_obj_tag(v___x_4998_) == 0)
{
size_t v___x_4999_; size_t v___x_5000_; 
lean_dec_ref_known(v___x_4998_, 1);
v___x_4999_ = ((size_t)1ULL);
v___x_5000_ = lean_usize_add(v_i_4977_, v___x_4999_);
v_i_4977_ = v___x_5000_;
v_b_4978_ = v___x_4987_;
goto _start;
}
else
{
return v___x_4998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object* v_as_5012_, lean_object* v_sz_5013_, lean_object* v_i_5014_, lean_object* v_b_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_){
_start:
{
size_t v_sz_boxed_5022_; size_t v_i_boxed_5023_; lean_object* v_res_5024_; 
v_sz_boxed_5022_ = lean_unbox_usize(v_sz_5013_);
lean_dec(v_sz_5013_);
v_i_boxed_5023_ = lean_unbox_usize(v_i_5014_);
lean_dec(v_i_5014_);
v_res_5024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5012_, v_sz_boxed_5022_, v_i_boxed_5023_, v_b_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v_as_5012_);
return v_res_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object* v_stx_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v_ids_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; 
v___x_5035_ = lean_unsigned_to_nat(1u);
v___x_5036_ = l_Lean_Syntax_getArg(v_stx_5025_, v___x_5035_);
v_ids_5037_ = l_Lean_Syntax_getArgs(v___x_5036_);
lean_dec(v___x_5036_);
v___x_5038_ = lean_array_get_size(v_ids_5037_);
v___x_5039_ = lean_unsigned_to_nat(0u);
v___x_5040_ = lean_nat_dec_eq(v___x_5038_, v___x_5039_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; size_t v_sz_5042_; size_t v___x_5043_; lean_object* v___x_5044_; 
v___x_5041_ = lean_box(0);
v_sz_5042_ = lean_array_size(v_ids_5037_);
v___x_5043_ = ((size_t)0ULL);
v___x_5044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_ids_5037_, v_sz_5042_, v___x_5043_, v___x_5041_, v_a_5027_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
lean_dec_ref(v_ids_5037_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5051_ == 0)
{
lean_object* v_unused_5052_; 
v_unused_5052_ = lean_ctor_get(v___x_5044_, 0);
lean_dec(v_unused_5052_);
v___x_5046_ = v___x_5044_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_dec(v___x_5044_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
lean_ctor_set(v___x_5046_, 0, v___x_5041_);
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5041_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
else
{
return v___x_5044_;
}
}
else
{
lean_object* v___x_5053_; lean_object* v___x_5054_; 
lean_dec_ref(v_ids_5037_);
v___x_5053_ = lean_box(0);
v___x_5054_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___x_5053_, v_a_5027_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
return v___x_5054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object* v_stx_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l_Lean_Elab_Tactic_Conv_evalExt(v_stx_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
lean_dec(v_a_5061_);
lean_dec_ref(v_a_5060_);
lean_dec(v_a_5059_);
lean_dec_ref(v_a_5058_);
lean_dec(v_a_5057_);
lean_dec_ref(v_a_5056_);
lean_dec(v_stx_5055_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object* v_as_5066_, size_t v_sz_5067_, size_t v_i_5068_, lean_object* v_b_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v___x_5079_; 
v___x_5079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5066_, v_sz_5067_, v_i_5068_, v_b_5069_, v___y_5071_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object* v_as_5080_, lean_object* v_sz_5081_, lean_object* v_i_5082_, lean_object* v_b_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_){
_start:
{
size_t v_sz_boxed_5093_; size_t v_i_boxed_5094_; lean_object* v_res_5095_; 
v_sz_boxed_5093_ = lean_unbox_usize(v_sz_5081_);
lean_dec(v_sz_5081_);
v_i_boxed_5094_ = lean_unbox_usize(v_i_5082_);
lean_dec(v_i_5082_);
v_res_5095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(v_as_5080_, v_sz_boxed_5093_, v_i_boxed_5094_, v_b_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec_ref(v_as_5080_);
return v_res_5095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1(){
_start:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; 
v___x_5110_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0));
v___x_5112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5113_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExt___boxed), 10, 0);
v___x_5114_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5110_, v___x_5111_, v___x_5112_, v___x_5113_);
return v___x_5114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object* v_a_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3(){
_start:
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6));
v___x_5145_ = l_Lean_addBuiltinDeclarationRanges(v___x_5143_, v___x_5144_);
return v___x_5145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object* v_a_5146_){
_start:
{
lean_object* v_res_5147_; 
v_res_5147_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
return v_res_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object* v_a_5148_, lean_object* v_trees_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v___x_5159_; 
lean_inc(v___y_5157_);
lean_inc_ref(v___y_5156_);
lean_inc(v___y_5155_);
lean_inc_ref(v___y_5154_);
lean_inc(v___y_5153_);
lean_inc_ref(v___y_5152_);
lean_inc(v___y_5151_);
lean_inc_ref(v___y_5150_);
v___x_5159_ = lean_apply_9(v_a_5148_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, lean_box(0));
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5168_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5162_ = v___x_5159_;
v_isShared_5163_ = v_isSharedCheck_5168_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v___x_5159_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5168_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5164_; lean_object* v___x_5166_; 
v___x_5164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5164_, 0, v_a_5160_);
lean_ctor_set(v___x_5164_, 1, v_trees_5149_);
if (v_isShared_5163_ == 0)
{
lean_ctor_set(v___x_5162_, 0, v___x_5164_);
v___x_5166_ = v___x_5162_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
else
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5176_; 
lean_dec_ref(v_trees_5149_);
v_a_5169_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5171_ = v___x_5159_;
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5159_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5176_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5174_; 
if (v_isShared_5172_ == 0)
{
v___x_5174_ = v___x_5171_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object* v_a_5177_, lean_object* v_trees_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(v_a_5177_, v_trees_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec_ref(v___y_5181_);
lean_dec(v___y_5180_);
lean_dec_ref(v___y_5179_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object* v___x_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5189_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object* v___x_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(v___x_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
lean_dec(v___y_5202_);
lean_dec_ref(v___y_5201_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(uint8_t v___x_5211_, lean_object* v___x_5212_, lean_object* v___x_5213_, lean_object* v___x_5214_, lean_object* v___x_5215_, lean_object* v___x_5216_, lean_object* v___x_5217_, lean_object* v___x_5218_, lean_object* v___x_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
if (v___x_5211_ == 0)
{
lean_object* v___x_5229_; 
lean_dec_ref(v___y_5226_);
lean_dec(v___x_5219_);
lean_dec_ref(v___x_5218_);
lean_dec_ref(v___x_5217_);
lean_dec_ref(v___x_5216_);
lean_dec_ref(v___x_5215_);
v___x_5229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5212_);
return v___x_5229_;
}
else
{
lean_object* v_toCold_5230_; lean_object* v_currRecDepth_5231_; lean_object* v_ref_5232_; uint8_t v_diag_5233_; uint8_t v_suppressElabErrors_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5264_; 
v_toCold_5230_ = lean_ctor_get(v___y_5226_, 0);
v_currRecDepth_5231_ = lean_ctor_get(v___y_5226_, 1);
v_ref_5232_ = lean_ctor_get(v___y_5226_, 2);
v_diag_5233_ = lean_ctor_get_uint8(v___y_5226_, sizeof(void*)*3);
v_suppressElabErrors_5234_ = lean_ctor_get_uint8(v___y_5226_, sizeof(void*)*3 + 1);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___y_5226_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5236_ = v___y_5226_;
v_isShared_5237_ = v_isSharedCheck_5264_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_ref_5232_);
lean_inc(v_currRecDepth_5231_);
lean_inc(v_toCold_5230_);
lean_dec(v___y_5226_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5264_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v_ref_5238_; lean_object* v___x_5240_; 
v_ref_5238_ = l_Lean_replaceRef(v___x_5213_, v_ref_5232_);
lean_dec(v_ref_5232_);
lean_inc(v_ref_5238_);
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 2, v_ref_5238_);
v___x_5240_ = v___x_5236_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_toCold_5230_);
lean_ctor_set(v_reuseFailAlloc_5263_, 1, v_currRecDepth_5231_);
lean_ctor_set(v_reuseFailAlloc_5263_, 2, v_ref_5238_);
lean_ctor_set_uint8(v_reuseFailAlloc_5263_, sizeof(void*)*3, v_diag_5233_);
lean_ctor_set_uint8(v_reuseFailAlloc_5263_, sizeof(void*)*3 + 1, v_suppressElabErrors_5234_);
v___x_5240_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; uint8_t v___x_5244_; 
v___x_5241_ = l_Lean_Syntax_getArg(v___x_5213_, v___x_5214_);
v___x_5242_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__2));
lean_inc_ref(v___x_5218_);
lean_inc_ref(v___x_5217_);
lean_inc_ref(v___x_5216_);
lean_inc_ref(v___x_5215_);
v___x_5243_ = l_Lean_Name_mkStr5(v___x_5215_, v___x_5216_, v___x_5217_, v___x_5218_, v___x_5242_);
lean_inc(v___x_5241_);
v___x_5244_ = l_Lean_Syntax_isOfKind(v___x_5241_, v___x_5243_);
lean_dec(v___x_5243_);
if (v___x_5244_ == 0)
{
lean_object* v___x_5245_; lean_object* v___x_5246_; uint8_t v___x_5247_; 
v___x_5245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0));
lean_inc_ref(v___x_5215_);
v___x_5246_ = l_Lean_Name_mkStr2(v___x_5215_, v___x_5245_);
lean_inc(v___x_5241_);
v___x_5247_ = l_Lean_Syntax_isOfKind(v___x_5241_, v___x_5246_);
lean_dec(v___x_5246_);
if (v___x_5247_ == 0)
{
lean_object* v___x_5248_; 
lean_dec(v___x_5241_);
lean_dec_ref(v___x_5240_);
lean_dec(v_ref_5238_);
lean_dec(v___x_5219_);
lean_dec_ref(v___x_5218_);
lean_dec_ref(v___x_5217_);
lean_dec_ref(v___x_5216_);
lean_dec_ref(v___x_5215_);
v___x_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5212_);
return v___x_5248_;
}
else
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v___x_5249_ = l_Lean_SourceInfo_fromRef(v_ref_5238_, v___x_5244_);
lean_dec(v_ref_5238_);
v___x_5250_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_5251_ = l_Lean_Name_mkStr5(v___x_5215_, v___x_5216_, v___x_5217_, v___x_5218_, v___x_5250_);
lean_inc_n(v___x_5249_, 2);
v___x_5252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5249_);
lean_ctor_set(v___x_5252_, 1, v___x_5250_);
v___x_5253_ = l_Lean_Syntax_node1(v___x_5249_, v___x_5219_, v___x_5241_);
v___x_5254_ = l_Lean_Syntax_node2(v___x_5249_, v___x_5251_, v___x_5252_, v___x_5253_);
v___x_5255_ = l_Lean_Elab_Tactic_evalTactic(v___x_5254_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___x_5240_, v___y_5227_);
lean_dec_ref(v___x_5240_);
return v___x_5255_;
}
}
else
{
uint8_t v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; 
lean_dec(v___x_5219_);
v___x_5256_ = 0;
v___x_5257_ = l_Lean_SourceInfo_fromRef(v_ref_5238_, v___x_5256_);
lean_dec(v_ref_5238_);
v___x_5258_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_5259_ = l_Lean_Name_mkStr5(v___x_5215_, v___x_5216_, v___x_5217_, v___x_5218_, v___x_5258_);
lean_inc(v___x_5257_);
v___x_5260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5257_);
lean_ctor_set(v___x_5260_, 1, v___x_5258_);
v___x_5261_ = l_Lean_Syntax_node2(v___x_5257_, v___x_5259_, v___x_5260_, v___x_5241_);
v___x_5262_ = l_Lean_Elab_Tactic_evalTactic(v___x_5261_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___x_5240_, v___y_5227_);
lean_dec_ref(v___x_5240_);
return v___x_5262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_5265_ = _args[0];
lean_object* v___x_5266_ = _args[1];
lean_object* v___x_5267_ = _args[2];
lean_object* v___x_5268_ = _args[3];
lean_object* v___x_5269_ = _args[4];
lean_object* v___x_5270_ = _args[5];
lean_object* v___x_5271_ = _args[6];
lean_object* v___x_5272_ = _args[7];
lean_object* v___x_5273_ = _args[8];
lean_object* v___y_5274_ = _args[9];
lean_object* v___y_5275_ = _args[10];
lean_object* v___y_5276_ = _args[11];
lean_object* v___y_5277_ = _args[12];
lean_object* v___y_5278_ = _args[13];
lean_object* v___y_5279_ = _args[14];
lean_object* v___y_5280_ = _args[15];
lean_object* v___y_5281_ = _args[16];
lean_object* v___y_5282_ = _args[17];
_start:
{
uint8_t v___x_15583__boxed_5283_; lean_object* v_res_5284_; 
v___x_15583__boxed_5283_ = lean_unbox(v___x_5265_);
v_res_5284_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(v___x_15583__boxed_5283_, v___x_5266_, v___x_5267_, v___x_5268_, v___x_5269_, v___x_5270_, v___x_5271_, v___x_5272_, v___x_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_);
lean_dec(v___y_5281_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v___y_5274_);
lean_dec(v___x_5268_);
lean_dec(v___x_5267_);
return v_res_5284_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(lean_object* v_a_5285_, lean_object* v_trees_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v___x_5296_; 
lean_inc(v___y_5294_);
lean_inc_ref(v___y_5293_);
lean_inc(v___y_5292_);
lean_inc_ref(v___y_5291_);
lean_inc(v___y_5290_);
lean_inc_ref(v___y_5289_);
lean_inc(v___y_5288_);
lean_inc_ref(v___y_5287_);
v___x_5296_ = lean_apply_9(v_a_5285_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, lean_box(0));
if (lean_obj_tag(v___x_5296_) == 0)
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5305_; 
v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5299_ = v___x_5296_;
v_isShared_5300_ = v_isSharedCheck_5305_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___x_5296_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5305_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5301_, 0, v_a_5297_);
lean_ctor_set(v___x_5301_, 1, v_trees_5286_);
if (v_isShared_5300_ == 0)
{
lean_ctor_set(v___x_5299_, 0, v___x_5301_);
v___x_5303_ = v___x_5299_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
else
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
lean_dec_ref(v_trees_5286_);
v_a_5306_ = lean_ctor_get(v___x_5296_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5296_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5296_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5296_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object* v_a_5314_, lean_object* v_trees_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v_res_5325_; 
v_res_5325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(v_a_5314_, v_trees_5315_, v___y_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
lean_dec(v___y_5323_);
lean_dec_ref(v___y_5322_);
lean_dec(v___y_5321_);
lean_dec_ref(v___y_5320_);
lean_dec(v___y_5319_);
lean_dec_ref(v___y_5318_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
return v_res_5325_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; 
v___x_5326_ = lean_unsigned_to_nat(32u);
v___x_5327_ = lean_mk_empty_array_with_capacity(v___x_5326_);
v___x_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5327_);
return v___x_5328_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5329_ = ((size_t)5ULL);
v___x_5330_ = lean_unsigned_to_nat(0u);
v___x_5331_ = lean_unsigned_to_nat(32u);
v___x_5332_ = lean_mk_empty_array_with_capacity(v___x_5331_);
v___x_5333_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0);
v___x_5334_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5334_, 0, v___x_5333_);
lean_ctor_set(v___x_5334_, 1, v___x_5332_);
lean_ctor_set(v___x_5334_, 2, v___x_5330_);
lean_ctor_set(v___x_5334_, 3, v___x_5330_);
lean_ctor_set_usize(v___x_5334_, 4, v___x_5329_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object* v___y_5335_){
_start:
{
lean_object* v___x_5337_; lean_object* v_infoState_5338_; lean_object* v_trees_5339_; lean_object* v___x_5340_; lean_object* v_infoState_5341_; lean_object* v_env_5342_; lean_object* v_nextMacroScope_5343_; lean_object* v_ngen_5344_; lean_object* v_auxDeclNGen_5345_; lean_object* v_traceState_5346_; lean_object* v_cache_5347_; lean_object* v_messages_5348_; lean_object* v_snapshotTasks_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5370_; 
v___x_5337_ = lean_st_ref_get(v___y_5335_);
v_infoState_5338_ = lean_ctor_get(v___x_5337_, 7);
lean_inc_ref(v_infoState_5338_);
lean_dec(v___x_5337_);
v_trees_5339_ = lean_ctor_get(v_infoState_5338_, 2);
lean_inc_ref(v_trees_5339_);
lean_dec_ref(v_infoState_5338_);
v___x_5340_ = lean_st_ref_take(v___y_5335_);
v_infoState_5341_ = lean_ctor_get(v___x_5340_, 7);
v_env_5342_ = lean_ctor_get(v___x_5340_, 0);
v_nextMacroScope_5343_ = lean_ctor_get(v___x_5340_, 1);
v_ngen_5344_ = lean_ctor_get(v___x_5340_, 2);
v_auxDeclNGen_5345_ = lean_ctor_get(v___x_5340_, 3);
v_traceState_5346_ = lean_ctor_get(v___x_5340_, 4);
v_cache_5347_ = lean_ctor_get(v___x_5340_, 5);
v_messages_5348_ = lean_ctor_get(v___x_5340_, 6);
v_snapshotTasks_5349_ = lean_ctor_get(v___x_5340_, 8);
v_isSharedCheck_5370_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5351_ = v___x_5340_;
v_isShared_5352_ = v_isSharedCheck_5370_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_snapshotTasks_5349_);
lean_inc(v_infoState_5341_);
lean_inc(v_messages_5348_);
lean_inc(v_cache_5347_);
lean_inc(v_traceState_5346_);
lean_inc(v_auxDeclNGen_5345_);
lean_inc(v_ngen_5344_);
lean_inc(v_nextMacroScope_5343_);
lean_inc(v_env_5342_);
lean_dec(v___x_5340_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5370_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
uint8_t v_enabled_5353_; lean_object* v_assignment_5354_; lean_object* v_lazyAssignment_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5368_; 
v_enabled_5353_ = lean_ctor_get_uint8(v_infoState_5341_, sizeof(void*)*3);
v_assignment_5354_ = lean_ctor_get(v_infoState_5341_, 0);
v_lazyAssignment_5355_ = lean_ctor_get(v_infoState_5341_, 1);
v_isSharedCheck_5368_ = !lean_is_exclusive(v_infoState_5341_);
if (v_isSharedCheck_5368_ == 0)
{
lean_object* v_unused_5369_; 
v_unused_5369_ = lean_ctor_get(v_infoState_5341_, 2);
lean_dec(v_unused_5369_);
v___x_5357_ = v_infoState_5341_;
v_isShared_5358_ = v_isSharedCheck_5368_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_lazyAssignment_5355_);
lean_inc(v_assignment_5354_);
lean_dec(v_infoState_5341_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5368_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5359_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 2, v___x_5359_);
v___x_5361_ = v___x_5357_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_assignment_5354_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v_lazyAssignment_5355_);
lean_ctor_set(v_reuseFailAlloc_5367_, 2, v___x_5359_);
lean_ctor_set_uint8(v_reuseFailAlloc_5367_, sizeof(void*)*3, v_enabled_5353_);
v___x_5361_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
lean_object* v___x_5363_; 
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 7, v___x_5361_);
v___x_5363_ = v___x_5351_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_env_5342_);
lean_ctor_set(v_reuseFailAlloc_5366_, 1, v_nextMacroScope_5343_);
lean_ctor_set(v_reuseFailAlloc_5366_, 2, v_ngen_5344_);
lean_ctor_set(v_reuseFailAlloc_5366_, 3, v_auxDeclNGen_5345_);
lean_ctor_set(v_reuseFailAlloc_5366_, 4, v_traceState_5346_);
lean_ctor_set(v_reuseFailAlloc_5366_, 5, v_cache_5347_);
lean_ctor_set(v_reuseFailAlloc_5366_, 6, v_messages_5348_);
lean_ctor_set(v_reuseFailAlloc_5366_, 7, v___x_5361_);
lean_ctor_set(v_reuseFailAlloc_5366_, 8, v_snapshotTasks_5349_);
v___x_5363_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5364_ = lean_st_ref_put(v___y_5335_, v___x_5363_);
v___x_5365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5365_, 0, v_trees_5339_);
return v___x_5365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object* v___y_5371_, lean_object* v___y_5372_){
_start:
{
lean_object* v_res_5373_; 
v_res_5373_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5371_);
lean_dec(v___y_5371_);
return v_res_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object* v___y_5374_, lean_object* v_mkInfoTree_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v_a_5383_, lean_object* v_a_x3f_5384_){
_start:
{
lean_object* v___x_5386_; lean_object* v_infoState_5387_; lean_object* v_trees_5388_; lean_object* v___x_5389_; 
v___x_5386_ = lean_st_ref_get(v___y_5374_);
v_infoState_5387_ = lean_ctor_get(v___x_5386_, 7);
lean_inc_ref(v_infoState_5387_);
lean_dec(v___x_5386_);
v_trees_5388_ = lean_ctor_get(v_infoState_5387_, 2);
lean_inc_ref(v_trees_5388_);
lean_dec_ref(v_infoState_5387_);
lean_inc(v___y_5374_);
lean_inc_ref(v___y_5382_);
lean_inc(v___y_5381_);
lean_inc_ref(v___y_5380_);
lean_inc(v___y_5379_);
lean_inc_ref(v___y_5378_);
lean_inc(v___y_5377_);
lean_inc_ref(v___y_5376_);
v___x_5389_ = lean_apply_10(v_mkInfoTree_5375_, v_trees_5388_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5374_, lean_box(0));
if (lean_obj_tag(v___x_5389_) == 0)
{
lean_object* v_a_5390_; lean_object* v___x_5392_; uint8_t v_isShared_5393_; uint8_t v_isSharedCheck_5428_; 
v_a_5390_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5392_ = v___x_5389_;
v_isShared_5393_ = v_isSharedCheck_5428_;
goto v_resetjp_5391_;
}
else
{
lean_inc(v_a_5390_);
lean_dec(v___x_5389_);
v___x_5392_ = lean_box(0);
v_isShared_5393_ = v_isSharedCheck_5428_;
goto v_resetjp_5391_;
}
v_resetjp_5391_:
{
lean_object* v___x_5394_; lean_object* v_infoState_5395_; lean_object* v_env_5396_; lean_object* v_nextMacroScope_5397_; lean_object* v_ngen_5398_; lean_object* v_auxDeclNGen_5399_; lean_object* v_traceState_5400_; lean_object* v_cache_5401_; lean_object* v_messages_5402_; lean_object* v_snapshotTasks_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5427_; 
v___x_5394_ = lean_st_ref_take(v___y_5374_);
v_infoState_5395_ = lean_ctor_get(v___x_5394_, 7);
v_env_5396_ = lean_ctor_get(v___x_5394_, 0);
v_nextMacroScope_5397_ = lean_ctor_get(v___x_5394_, 1);
v_ngen_5398_ = lean_ctor_get(v___x_5394_, 2);
v_auxDeclNGen_5399_ = lean_ctor_get(v___x_5394_, 3);
v_traceState_5400_ = lean_ctor_get(v___x_5394_, 4);
v_cache_5401_ = lean_ctor_get(v___x_5394_, 5);
v_messages_5402_ = lean_ctor_get(v___x_5394_, 6);
v_snapshotTasks_5403_ = lean_ctor_get(v___x_5394_, 8);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5394_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5405_ = v___x_5394_;
v_isShared_5406_ = v_isSharedCheck_5427_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_snapshotTasks_5403_);
lean_inc(v_infoState_5395_);
lean_inc(v_messages_5402_);
lean_inc(v_cache_5401_);
lean_inc(v_traceState_5400_);
lean_inc(v_auxDeclNGen_5399_);
lean_inc(v_ngen_5398_);
lean_inc(v_nextMacroScope_5397_);
lean_inc(v_env_5396_);
lean_dec(v___x_5394_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5427_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
uint8_t v_enabled_5407_; lean_object* v_assignment_5408_; lean_object* v_lazyAssignment_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5425_; 
v_enabled_5407_ = lean_ctor_get_uint8(v_infoState_5395_, sizeof(void*)*3);
v_assignment_5408_ = lean_ctor_get(v_infoState_5395_, 0);
v_lazyAssignment_5409_ = lean_ctor_get(v_infoState_5395_, 1);
v_isSharedCheck_5425_ = !lean_is_exclusive(v_infoState_5395_);
if (v_isSharedCheck_5425_ == 0)
{
lean_object* v_unused_5426_; 
v_unused_5426_ = lean_ctor_get(v_infoState_5395_, 2);
lean_dec(v_unused_5426_);
v___x_5411_ = v_infoState_5395_;
v_isShared_5412_ = v_isSharedCheck_5425_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_lazyAssignment_5409_);
lean_inc(v_assignment_5408_);
lean_dec(v_infoState_5395_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5425_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5413_; lean_object* v___x_5415_; 
v___x_5413_ = l_Lean_PersistentArray_push___redArg(v_a_5383_, v_a_5390_);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 2, v___x_5413_);
v___x_5415_ = v___x_5411_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_assignment_5408_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v_lazyAssignment_5409_);
lean_ctor_set(v_reuseFailAlloc_5424_, 2, v___x_5413_);
lean_ctor_set_uint8(v_reuseFailAlloc_5424_, sizeof(void*)*3, v_enabled_5407_);
v___x_5415_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
lean_object* v___x_5417_; 
if (v_isShared_5406_ == 0)
{
lean_ctor_set(v___x_5405_, 7, v___x_5415_);
v___x_5417_ = v___x_5405_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v_env_5396_);
lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_nextMacroScope_5397_);
lean_ctor_set(v_reuseFailAlloc_5423_, 2, v_ngen_5398_);
lean_ctor_set(v_reuseFailAlloc_5423_, 3, v_auxDeclNGen_5399_);
lean_ctor_set(v_reuseFailAlloc_5423_, 4, v_traceState_5400_);
lean_ctor_set(v_reuseFailAlloc_5423_, 5, v_cache_5401_);
lean_ctor_set(v_reuseFailAlloc_5423_, 6, v_messages_5402_);
lean_ctor_set(v_reuseFailAlloc_5423_, 7, v___x_5415_);
lean_ctor_set(v_reuseFailAlloc_5423_, 8, v_snapshotTasks_5403_);
v___x_5417_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5421_; 
v___x_5418_ = lean_st_ref_put(v___y_5374_, v___x_5417_);
v___x_5419_ = lean_box(0);
if (v_isShared_5393_ == 0)
{
lean_ctor_set(v___x_5392_, 0, v___x_5419_);
v___x_5421_ = v___x_5392_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5419_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
lean_dec_ref(v_a_5383_);
v_a_5429_ = lean_ctor_get(v___x_5389_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5389_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5389_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5389_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object* v___y_5437_, lean_object* v_mkInfoTree_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v_a_5446_, lean_object* v_a_x3f_5447_, lean_object* v___y_5448_){
_start:
{
lean_object* v_res_5449_; 
v_res_5449_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5437_, v_mkInfoTree_5438_, v___y_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v_a_5446_, v_a_x3f_5447_);
lean_dec(v_a_x3f_5447_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5442_);
lean_dec_ref(v___y_5441_);
lean_dec(v___y_5440_);
lean_dec_ref(v___y_5439_);
lean_dec(v___y_5437_);
return v_res_5449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object* v_x_5450_, lean_object* v_mkInfoTree_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_){
_start:
{
lean_object* v___x_5461_; lean_object* v_infoState_5462_; uint8_t v_enabled_5463_; 
v___x_5461_ = lean_st_ref_get(v___y_5459_);
v_infoState_5462_ = lean_ctor_get(v___x_5461_, 7);
lean_inc_ref(v_infoState_5462_);
lean_dec(v___x_5461_);
v_enabled_5463_ = lean_ctor_get_uint8(v_infoState_5462_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5462_);
if (v_enabled_5463_ == 0)
{
lean_object* v___x_5464_; 
lean_dec_ref(v_mkInfoTree_5451_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
lean_inc(v___y_5455_);
lean_inc_ref(v___y_5454_);
lean_inc(v___y_5453_);
lean_inc_ref(v___y_5452_);
v___x_5464_ = lean_apply_9(v_x_5450_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, lean_box(0));
return v___x_5464_;
}
else
{
lean_object* v___x_5465_; lean_object* v_a_5466_; lean_object* v_r_5467_; 
v___x_5465_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5459_);
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc(v_a_5466_);
lean_dec_ref(v___x_5465_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
lean_inc(v___y_5455_);
lean_inc_ref(v___y_5454_);
lean_inc(v___y_5453_);
lean_inc_ref(v___y_5452_);
v_r_5467_ = lean_apply_9(v_x_5450_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, lean_box(0));
if (lean_obj_tag(v_r_5467_) == 0)
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5492_; 
v_a_5468_ = lean_ctor_get(v_r_5467_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v_r_5467_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5470_ = v_r_5467_;
v_isShared_5471_ = v_isSharedCheck_5492_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v_r_5467_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5492_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
lean_inc(v_a_5468_);
if (v_isShared_5471_ == 0)
{
lean_ctor_set_tag(v___x_5470_, 1);
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5474_; 
v___x_5474_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5459_, v_mkInfoTree_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v_a_5466_, v___x_5473_);
lean_dec_ref(v___x_5473_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5481_; 
v_isSharedCheck_5481_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5481_ == 0)
{
lean_object* v_unused_5482_; 
v_unused_5482_ = lean_ctor_get(v___x_5474_, 0);
lean_dec(v_unused_5482_);
v___x_5476_ = v___x_5474_;
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
else
{
lean_dec(v___x_5474_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5481_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5479_; 
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v_a_5468_);
v___x_5479_ = v___x_5476_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_a_5468_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
else
{
lean_object* v_a_5483_; lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5490_; 
lean_dec(v_a_5468_);
v_a_5483_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5490_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5490_ == 0)
{
v___x_5485_ = v___x_5474_;
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
else
{
lean_inc(v_a_5483_);
lean_dec(v___x_5474_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5490_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5488_; 
if (v_isShared_5486_ == 0)
{
v___x_5488_ = v___x_5485_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_a_5483_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
}
}
}
else
{
lean_object* v_a_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
v_a_5493_ = lean_ctor_get(v_r_5467_, 0);
lean_inc(v_a_5493_);
lean_dec_ref_known(v_r_5467_, 1);
v___x_5494_ = lean_box(0);
v___x_5495_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5459_, v_mkInfoTree_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v_a_5466_, v___x_5494_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5502_; 
v_isSharedCheck_5502_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5502_ == 0)
{
lean_object* v_unused_5503_; 
v_unused_5503_ = lean_ctor_get(v___x_5495_, 0);
lean_dec(v_unused_5503_);
v___x_5497_ = v___x_5495_;
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
else
{
lean_dec(v___x_5495_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5500_; 
if (v_isShared_5498_ == 0)
{
lean_ctor_set_tag(v___x_5497_, 1);
lean_ctor_set(v___x_5497_, 0, v_a_5493_);
v___x_5500_ = v___x_5497_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5493_);
v___x_5500_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
return v___x_5500_;
}
}
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec(v_a_5493_);
v_a_5504_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___x_5495_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5495_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object* v_x_5512_, lean_object* v_mkInfoTree_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_){
_start:
{
lean_object* v_res_5523_; 
v_res_5523_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5512_, v_mkInfoTree_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
lean_dec(v___y_5515_);
lean_dec_ref(v___y_5514_);
return v_res_5523_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object* v_upperBound_5534_, lean_object* v_enterArgsAndSeps_5535_, lean_object* v_a_5536_, lean_object* v_b_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_){
_start:
{
uint8_t v___x_5547_; 
v___x_5547_ = lean_nat_dec_lt(v_a_5536_, v_upperBound_5534_);
if (v___x_5547_ == 0)
{
lean_object* v___x_5548_; 
lean_dec(v_a_5536_);
v___x_5548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5548_, 0, v_b_5537_);
return v___x_5548_;
}
else
{
lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___y_5557_; lean_object* v___x_5586_; lean_object* v___x_5587_; uint8_t v___x_5588_; 
v___x_5549_ = lean_unsigned_to_nat(2u);
v___x_5550_ = lean_box(0);
v___x_5551_ = lean_box(0);
v___x_5552_ = lean_unsigned_to_nat(0u);
v___x_5553_ = lean_unsigned_to_nat(1u);
v___x_5554_ = lean_nat_mul(v___x_5549_, v_a_5536_);
v___x_5555_ = lean_array_get_borrowed(v___x_5550_, v_enterArgsAndSeps_5535_, v___x_5554_);
v___x_5586_ = lean_nat_add(v___x_5554_, v___x_5553_);
lean_dec(v___x_5554_);
v___x_5587_ = lean_array_get_size(v_enterArgsAndSeps_5535_);
v___x_5588_ = lean_nat_dec_lt(v___x_5586_, v___x_5587_);
if (v___x_5588_ == 0)
{
lean_dec(v___x_5586_);
v___y_5557_ = v___x_5550_;
goto v___jp_5556_;
}
else
{
lean_object* v___x_5589_; 
v___x_5589_ = lean_array_fget_borrowed(v_enterArgsAndSeps_5535_, v___x_5586_);
lean_dec(v___x_5586_);
lean_inc(v___x_5589_);
v___y_5557_ = v___x_5589_;
goto v___jp_5556_;
}
v___jp_5556_:
{
lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; 
v___x_5558_ = lean_mk_empty_array_with_capacity(v___x_5549_);
lean_inc(v___x_5555_);
v___x_5559_ = lean_array_push(v___x_5558_, v___x_5555_);
v___x_5560_ = lean_array_push(v___x_5559_, v___y_5557_);
v___x_5561_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5562_ = lean_box(2);
v___x_5563_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5563_, 0, v___x_5562_);
lean_ctor_set(v___x_5563_, 1, v___x_5561_);
lean_ctor_set(v___x_5563_, 2, v___x_5560_);
v___x_5564_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5563_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_);
if (lean_obj_tag(v___x_5564_) == 0)
{
lean_object* v_a_5565_; lean_object* v___f_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; uint8_t v___x_5572_; lean_object* v___x_5573_; lean_object* v___f_5574_; lean_object* v___x_5575_; 
v_a_5565_ = lean_ctor_get(v___x_5564_, 0);
lean_inc(v_a_5565_);
lean_dec_ref_known(v___x_5564_, 1);
v___f_5566_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5566_, 0, v_a_5565_);
v___x_5567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0));
v___x_5568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1));
v___x_5569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2));
v___x_5570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3));
v___x_5571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3));
lean_inc_n(v___x_5555_, 2);
v___x_5572_ = l_Lean_Syntax_isOfKind(v___x_5555_, v___x_5571_);
v___x_5573_ = lean_box(v___x_5572_);
v___f_5574_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed), 18, 9);
lean_closure_set(v___f_5574_, 0, v___x_5573_);
lean_closure_set(v___f_5574_, 1, v___x_5551_);
lean_closure_set(v___f_5574_, 2, v___x_5555_);
lean_closure_set(v___f_5574_, 3, v___x_5552_);
lean_closure_set(v___f_5574_, 4, v___x_5567_);
lean_closure_set(v___f_5574_, 5, v___x_5568_);
lean_closure_set(v___f_5574_, 6, v___x_5569_);
lean_closure_set(v___f_5574_, 7, v___x_5570_);
lean_closure_set(v___f_5574_, 8, v___x_5561_);
v___x_5575_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5574_, v___f_5566_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v___x_5576_; 
lean_dec_ref_known(v___x_5575_, 1);
v___x_5576_ = lean_nat_add(v_a_5536_, v___x_5553_);
lean_dec(v_a_5536_);
v_a_5536_ = v___x_5576_;
v_b_5537_ = v___x_5551_;
goto _start;
}
else
{
lean_dec(v_a_5536_);
return v___x_5575_;
}
}
else
{
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5585_; 
lean_dec(v_a_5536_);
v_a_5578_ = lean_ctor_get(v___x_5564_, 0);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5564_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5580_ = v___x_5564_;
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v___x_5564_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_a_5578_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object* v_upperBound_5590_, lean_object* v_enterArgsAndSeps_5591_, lean_object* v_a_5592_, lean_object* v_b_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_){
_start:
{
lean_object* v_res_5603_; 
v_res_5603_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5590_, v_enterArgsAndSeps_5591_, v_a_5592_, v_b_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
lean_dec(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec(v___y_5599_);
lean_dec_ref(v___y_5598_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
lean_dec_ref(v_enterArgsAndSeps_5591_);
lean_dec(v_upperBound_5590_);
return v_res_5603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object* v_stx_5606_, lean_object* v_a_5607_, lean_object* v_a_5608_, lean_object* v_a_5609_, lean_object* v_a_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_){
_start:
{
lean_object* v___x_5616_; lean_object* v_token_5617_; lean_object* v___x_5618_; lean_object* v_lbrak_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; 
v___x_5616_ = lean_unsigned_to_nat(0u);
v_token_5617_ = l_Lean_Syntax_getArg(v_stx_5606_, v___x_5616_);
v___x_5618_ = lean_unsigned_to_nat(1u);
v_lbrak_5619_ = l_Lean_Syntax_getArg(v_stx_5606_, v___x_5618_);
v___x_5620_ = lean_unsigned_to_nat(2u);
v___x_5621_ = lean_mk_empty_array_with_capacity(v___x_5620_);
v___x_5622_ = lean_array_push(v___x_5621_, v_token_5617_);
v___x_5623_ = lean_array_push(v___x_5622_, v_lbrak_5619_);
v___x_5624_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5625_ = lean_box(2);
v___x_5626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5625_);
lean_ctor_set(v___x_5626_, 1, v___x_5624_);
lean_ctor_set(v___x_5626_, 2, v___x_5623_);
v___x_5627_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5626_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_);
if (lean_obj_tag(v___x_5627_) == 0)
{
lean_object* v_a_5628_; lean_object* v___f_5629_; lean_object* v___x_5630_; lean_object* v___f_5631_; lean_object* v___x_5632_; 
v_a_5628_ = lean_ctor_get(v___x_5627_, 0);
lean_inc(v_a_5628_);
lean_dec_ref_known(v___x_5627_, 1);
v___f_5629_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5629_, 0, v_a_5628_);
v___x_5630_ = lean_box(0);
v___f_5631_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalEnter___closed__0));
v___x_5632_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5631_, v___f_5629_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_);
if (lean_obj_tag(v___x_5632_) == 0)
{
lean_object* v___x_5633_; lean_object* v_enterArgsAndSeps_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; 
lean_dec_ref_known(v___x_5632_, 1);
v___x_5633_ = l_Lean_Syntax_getArg(v_stx_5606_, v___x_5620_);
v_enterArgsAndSeps_5634_ = l_Lean_Syntax_getArgs(v___x_5633_);
lean_dec(v___x_5633_);
v___x_5635_ = lean_array_get_size(v_enterArgsAndSeps_5634_);
v___x_5636_ = lean_nat_add(v___x_5635_, v___x_5618_);
v___x_5637_ = lean_nat_shiftr(v___x_5636_, v___x_5618_);
lean_dec(v___x_5636_);
v___x_5638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v___x_5637_, v_enterArgsAndSeps_5634_, v___x_5616_, v___x_5630_, v_a_5607_, v_a_5608_, v_a_5609_, v_a_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_);
lean_dec_ref(v_enterArgsAndSeps_5634_);
lean_dec(v___x_5637_);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5645_; 
v_isSharedCheck_5645_ = !lean_is_exclusive(v___x_5638_);
if (v_isSharedCheck_5645_ == 0)
{
lean_object* v_unused_5646_; 
v_unused_5646_ = lean_ctor_get(v___x_5638_, 0);
lean_dec(v_unused_5646_);
v___x_5640_ = v___x_5638_;
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
else
{
lean_dec(v___x_5638_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
lean_object* v___x_5643_; 
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 0, v___x_5630_);
v___x_5643_ = v___x_5640_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v___x_5630_);
v___x_5643_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
return v___x_5643_;
}
}
}
else
{
return v___x_5638_;
}
}
else
{
return v___x_5632_;
}
}
else
{
lean_object* v_a_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5654_; 
v_a_5647_ = lean_ctor_get(v___x_5627_, 0);
v_isSharedCheck_5654_ = !lean_is_exclusive(v___x_5627_);
if (v_isSharedCheck_5654_ == 0)
{
v___x_5649_ = v___x_5627_;
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_a_5647_);
lean_dec(v___x_5627_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5652_; 
if (v_isShared_5650_ == 0)
{
v___x_5652_ = v___x_5649_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v_a_5647_);
v___x_5652_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
return v___x_5652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object* v_stx_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_){
_start:
{
lean_object* v_res_5665_; 
v_res_5665_ = l_Lean_Elab_Tactic_Conv_evalEnter(v_stx_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
lean_dec(v_a_5661_);
lean_dec_ref(v_a_5660_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
lean_dec(v_stx_5655_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5673_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object* v_00_u03b1_5686_, lean_object* v_x_5687_, lean_object* v_mkInfoTree_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_){
_start:
{
lean_object* v___x_5698_; 
v___x_5698_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5687_, v_mkInfoTree_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
return v___x_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object* v_00_u03b1_5699_, lean_object* v_x_5700_, lean_object* v_mkInfoTree_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_){
_start:
{
lean_object* v_res_5711_; 
v_res_5711_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(v_00_u03b1_5699_, v_x_5700_, v_mkInfoTree_5701_, v___y_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_);
lean_dec(v___y_5709_);
lean_dec_ref(v___y_5708_);
lean_dec(v___y_5707_);
lean_dec_ref(v___y_5706_);
lean_dec(v___y_5705_);
lean_dec_ref(v___y_5704_);
lean_dec(v___y_5703_);
lean_dec_ref(v___y_5702_);
return v_res_5711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object* v_upperBound_5712_, lean_object* v_enterArgsAndSeps_5713_, lean_object* v_inst_5714_, lean_object* v_R_5715_, lean_object* v_a_5716_, lean_object* v_b_5717_, lean_object* v_c_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
lean_object* v___x_5728_; 
v___x_5728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5712_, v_enterArgsAndSeps_5713_, v_a_5716_, v_b_5717_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
return v___x_5728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object* v_upperBound_5729_, lean_object* v_enterArgsAndSeps_5730_, lean_object* v_inst_5731_, lean_object* v_R_5732_, lean_object* v_a_5733_, lean_object* v_b_5734_, lean_object* v_c_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_){
_start:
{
lean_object* v_res_5745_; 
v_res_5745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(v_upperBound_5729_, v_enterArgsAndSeps_5730_, v_inst_5731_, v_R_5732_, v_a_5733_, v_b_5734_, v_c_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
lean_dec(v___y_5743_);
lean_dec_ref(v___y_5742_);
lean_dec(v___y_5741_);
lean_dec_ref(v___y_5740_);
lean_dec(v___y_5739_);
lean_dec_ref(v___y_5738_);
lean_dec(v___y_5737_);
lean_dec_ref(v___y_5736_);
lean_dec_ref(v_enterArgsAndSeps_5730_);
lean_dec(v_upperBound_5729_);
return v_res_5745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1(){
_start:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; 
v___x_5761_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1));
v___x_5763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3));
v___x_5764_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___boxed), 10, 0);
v___x_5765_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5761_, v___x_5762_, v___x_5763_, v___x_5764_);
return v___x_5765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object* v_a_5766_){
_start:
{
lean_object* v_res_5767_; 
v_res_5767_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
return v_res_5767_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Congr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Conv_Congr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Conv_Congr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Conv_Congr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Conv_Congr(builtin);
}
#ifdef __cplusplus
}
#endif
