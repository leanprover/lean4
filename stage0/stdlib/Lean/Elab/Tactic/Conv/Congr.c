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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
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
static const lean_string_object l_Lean_Elab_Tactic_Conv_elabArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Conv_elabArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "argArg"};
static const lean_object* l_Lean_Elab_Tactic_Conv_elabArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Conv_elabArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 211, 157, 2, 56, 142, 56, 136)}};
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object**);
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
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_mctx_95_; lean_object* v_lctx_96_; lean_object* v_options_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_88_);
v_mctx_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_mctx_95_);
lean_dec(v___x_94_);
v_lctx_96_ = lean_ctor_get(v___y_87_, 2);
v_options_97_ = lean_ctor_get(v___y_89_, 2);
lean_inc_ref(v_options_97_);
lean_inc_ref(v_lctx_96_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_env_93_);
lean_ctor_set(v___x_98_, 1, v_mctx_95_);
lean_ctor_set(v___x_98_, 2, v_lctx_96_);
lean_ctor_set(v___x_98_, 3, v_options_97_);
v___x_99_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_msgData_86_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0___boxed(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msgData_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_ref_114_; lean_object* v___x_115_; lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
v_ref_114_ = lean_ctor_get(v___y_111_, 5);
v___x_115_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_122_; 
lean_inc(v_ref_114_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_ref_114_);
lean_ctor_set(v___x_120_, 1, v_a_116_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 1);
lean_ctor_set(v___x_118_, 0, v___x_120_);
v___x_122_ = v___x_118_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg___boxed(lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
return v_res_131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object* v_mvarId_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1));
v___x_149_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_148_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_a_150_);
lean_dec_ref_known(v___x_149_, 1);
v___x_151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2));
v___x_152_ = lean_box(0);
v___x_153_ = l_Lean_MVarId_apply(v_mvarId_142_, v_a_150_, v___x_151_, v___x_152_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_158_; lean_object* v___y_159_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
if (lean_obj_tag(v_a_154_) == 1)
{
lean_object* v_tail_162_; 
v_tail_162_ = lean_ctor_get(v_a_154_, 1);
lean_inc(v_tail_162_);
if (lean_obj_tag(v_tail_162_) == 1)
{
lean_object* v_tail_163_; 
v_tail_163_ = lean_ctor_get(v_tail_162_, 1);
lean_inc(v_tail_163_);
if (lean_obj_tag(v_tail_163_) == 1)
{
lean_object* v_tail_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_209_; 
v_tail_164_ = lean_ctor_get(v_tail_163_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_tail_163_);
if (v_isSharedCheck_209_ == 0)
{
lean_object* v_unused_210_; 
v_unused_210_ = lean_ctor_get(v_tail_163_, 0);
lean_dec(v_unused_210_);
v___x_166_ = v_tail_163_;
v_isShared_167_ = v_isSharedCheck_209_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_tail_164_);
lean_dec(v_tail_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_209_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
if (lean_obj_tag(v_tail_164_) == 1)
{
lean_object* v_tail_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_207_; 
v_tail_168_ = lean_ctor_get(v_tail_164_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v_tail_164_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_tail_164_, 0);
lean_dec(v_unused_208_);
v___x_170_ = v_tail_164_;
v_isShared_171_ = v_isSharedCheck_207_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_tail_168_);
lean_dec(v_tail_164_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_207_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
if (lean_obj_tag(v_tail_168_) == 0)
{
lean_object* v_head_172_; lean_object* v_head_173_; lean_object* v___x_174_; 
v_head_172_ = lean_ctor_get(v_a_154_, 0);
lean_inc(v_head_172_);
lean_dec_ref_known(v_a_154_, 2);
v_head_173_ = lean_ctor_get(v_tail_162_, 0);
lean_inc(v_head_173_);
lean_dec_ref_known(v_tail_162_, 2);
v___x_174_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_172_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
v___x_176_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_173_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_190_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_190_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_190_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_190_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v_a_177_);
v___x_182_ = v___x_170_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_177_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_tail_168_);
v___x_182_ = v_reuseFailAlloc_189_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_182_);
lean_ctor_set(v___x_166_, 0, v_a_175_);
v___x_184_ = v___x_166_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_175_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_182_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_184_);
v___x_186_ = v___x_179_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_a_175_);
lean_del_object(v___x_170_);
lean_del_object(v___x_166_);
v_a_191_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_176_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_176_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_head_173_);
lean_del_object(v___x_170_);
lean_del_object(v___x_166_);
v_a_199_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_174_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_174_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_del_object(v___x_170_);
lean_dec(v_tail_168_);
lean_del_object(v___x_166_);
lean_dec_ref_known(v_tail_162_, 2);
lean_dec_ref_known(v_a_154_, 2);
v___y_156_ = v_a_143_;
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
goto v___jp_155_;
}
}
}
else
{
lean_del_object(v___x_166_);
lean_dec(v_tail_164_);
lean_dec_ref_known(v_tail_162_, 2);
lean_dec_ref_known(v_a_154_, 2);
v___y_156_ = v_a_143_;
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
goto v___jp_155_;
}
}
}
else
{
lean_dec_ref_known(v_tail_162_, 2);
lean_dec(v_tail_163_);
lean_dec_ref_known(v_a_154_, 2);
v___y_156_ = v_a_143_;
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
goto v___jp_155_;
}
}
else
{
lean_dec(v_tail_162_);
lean_dec_ref_known(v_a_154_, 2);
v___y_156_ = v_a_143_;
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
goto v___jp_155_;
}
}
else
{
lean_dec(v_a_154_);
v___y_156_ = v_a_143_;
v___y_157_ = v_a_144_;
v___y_158_ = v_a_145_;
v___y_159_ = v_a_146_;
goto v___jp_155_;
}
v___jp_155_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4);
v___x_161_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_160_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
return v___x_161_;
}
}
else
{
return v___x_153_;
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_mvarId_142_);
v_a_211_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_149_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_149_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object* v_mvarId_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object* v_00_u03b1_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object* v_00_u03b1_234_, lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(v_00_u03b1_234_, v_msg_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object* v_e_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = l_Lean_Expr_isArrow(v_e_242_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_box(v___x_248_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = l_Lean_Expr_bindingDomain_x21(v_e_242_);
v___x_252_ = l_Lean_Meta_isProp(v___x_251_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; uint8_t v___x_254_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
v___x_254_ = lean_unbox(v_a_253_);
lean_dec(v_a_253_);
if (v___x_254_ == 0)
{
return v___x_252_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_dec_ref_known(v___x_252_, 1);
v___x_255_ = l_Lean_Expr_bindingBody_x21(v_e_242_);
v___x_256_ = l_Lean_Meta_isProp(v___x_255_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
return v___x_256_;
}
}
else
{
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object* v_e_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v_e_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_a_258_);
lean_dec_ref(v_e_257_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___f_271_; lean_object* v___x_8673__overap_272_; lean_object* v___x_273_; 
v___f_271_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_8673__overap_272_ = lean_panic_fn_borrowed(v___f_271_, v_msg_265_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
v___x_273_ = lean_apply_5(v___x_8673__overap_272_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, lean_box(0));
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___boxed(lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v_msg_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(lean_object* v___x_281_, lean_object* v_fst_282_, lean_object* v_fst_283_, lean_object* v_fst_284_, lean_object* v_snd_285_, lean_object* v_tag_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_292_; 
lean_inc_ref(v___x_281_);
v___x_292_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_281_, v_tag_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_317_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_317_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_317_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_317_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_fst_297_; lean_object* v_snd_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_316_; 
v_fst_297_ = lean_ctor_get(v_a_293_, 0);
v_snd_298_ = lean_ctor_get(v_a_293_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_316_ == 0)
{
v___x_300_ = v_a_293_;
v_isShared_301_ = v_isSharedCheck_316_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snd_298_);
lean_inc(v_fst_297_);
lean_dec(v_a_293_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_316_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
lean_inc(v_fst_297_);
v___x_302_ = l_Lean_Expr_app___override(v_fst_282_, v_fst_297_);
lean_inc(v_snd_298_);
v___x_303_ = l_Lean_mkApp3(v_fst_283_, v___x_281_, v_fst_297_, v_snd_298_);
v___x_304_ = l_Lean_Expr_mvarId_x21(v_snd_298_);
lean_dec(v_snd_298_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_array_push(v_fst_284_, v___x_305_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_snd_285_);
lean_ctor_set(v___x_300_, 0, v___x_306_);
v___x_308_ = v___x_300_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_snd_285_);
v___x_308_ = v_reuseFailAlloc_315_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_303_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_302_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_311_);
v___x_313_ = v___x_295_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_snd_285_);
lean_dec(v_fst_284_);
lean_dec(v_fst_283_);
lean_dec(v_fst_282_);
lean_dec_ref(v___x_281_);
v_a_318_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_292_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_292_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1___boxed(lean_object* v___x_326_, lean_object* v_fst_327_, lean_object* v_fst_328_, lean_object* v_fst_329_, lean_object* v_snd_330_, lean_object* v_tag_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_326_, v_fst_327_, v_fst_328_, v_fst_329_, v_snd_330_, v_tag_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_337_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_341_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_342_ = lean_unsigned_to_nat(30u);
v___x_343_ = lean_unsigned_to_nat(68u);
v___x_344_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1));
v___x_345_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_346_ = l_mkPanicMessageWithDecl(v___x_345_, v___x_344_, v___x_343_, v___x_342_, v___x_341_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(lean_object* v_fst_347_, lean_object* v_snd_348_, lean_object* v_fst_349_, lean_object* v_fst_350_, lean_object* v_00___351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3);
v___x_358_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_357_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_369_; 
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_358_, 0);
lean_dec(v_unused_370_);
v___x_360_ = v___x_358_;
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
else
{
lean_dec(v___x_358_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_fst_347_);
lean_ctor_set(v___x_362_, 1, v_snd_348_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v_fst_349_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_fst_350_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_365_);
v___x_367_ = v___x_360_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec(v_fst_350_);
lean_dec(v_fst_349_);
lean_dec(v_snd_348_);
lean_dec(v_fst_347_);
v_a_371_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_358_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_358_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___boxed(lean_object* v_fst_379_, lean_object* v_snd_380_, lean_object* v_fst_381_, lean_object* v_fst_382_, lean_object* v_00___383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_379_, v_snd_380_, v_fst_381_, v_fst_382_, v_00___383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(lean_object* v_upperBound_390_, lean_object* v_args_391_, uint8_t v_nameSubgoals_392_, lean_object* v_origTag_393_, lean_object* v_a_394_, lean_object* v___x_395_, uint8_t v_addImplicitArgs_396_, lean_object* v_a_397_, lean_object* v_b_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_a_405_; lean_object* v___y_410_; uint8_t v___x_429_; 
v___x_429_ = lean_nat_dec_lt(v_a_397_, v_upperBound_390_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_b_398_);
return v___x_430_;
}
else
{
lean_object* v_snd_431_; lean_object* v_snd_432_; lean_object* v_fst_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_574_; 
v_snd_431_ = lean_ctor_get(v_b_398_, 1);
lean_inc(v_snd_431_);
v_snd_432_ = lean_ctor_get(v_snd_431_, 1);
lean_inc(v_snd_432_);
v_fst_433_ = lean_ctor_get(v_b_398_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_b_398_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_b_398_, 1);
lean_dec(v_unused_575_);
v___x_435_ = v_b_398_;
v_isShared_436_ = v_isSharedCheck_574_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_fst_433_);
lean_dec(v_b_398_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_574_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_fst_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_572_; 
v_fst_437_ = lean_ctor_get(v_snd_431_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_snd_431_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v_snd_431_, 1);
lean_dec(v_unused_573_);
v___x_439_ = v_snd_431_;
v_isShared_440_ = v_isSharedCheck_572_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_fst_437_);
lean_dec(v_snd_431_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_572_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_571_; 
v_fst_441_ = lean_ctor_get(v_snd_432_, 0);
v_snd_442_ = lean_ctor_get(v_snd_432_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_snd_432_);
if (v_isSharedCheck_571_ == 0)
{
v___x_444_ = v_snd_432_;
v_isShared_445_ = v_isSharedCheck_571_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_snd_442_);
lean_inc(v_fst_441_);
lean_dec(v_snd_432_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_571_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_paramInfo_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_paramInfo_446_ = lean_ctor_get(v_a_394_, 0);
v___x_447_ = l_Lean_instInhabitedExpr;
v___x_448_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_449_ = lean_array_get_borrowed(v___x_447_, v_args_391_, v_a_397_);
v___x_450_ = lean_array_get_borrowed(v___x_448_, v_paramInfo_446_, v_a_397_);
v___x_451_ = lean_array_fget_borrowed(v___x_395_, v_a_397_);
v___x_452_ = lean_unbox(v___x_451_);
switch(v___x_452_)
{
case 1:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_del_object(v___x_444_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
v___x_453_ = lean_box(0);
v___x_454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_441_, v_snd_442_, v_fst_437_, v_fst_433_, v___x_453_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v___y_410_ = v___x_454_;
goto v___jp_409_;
}
case 2:
{
if (v_addImplicitArgs_396_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_450_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_inc_n(v___x_449_, 2);
v___x_481_ = l_Lean_Expr_app___override(v_fst_433_, v___x_449_);
v___x_482_ = l_Lean_Meta_mkEqRefl(v___x_449_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
lean_inc_n(v___x_449_, 2);
v___x_484_ = l_Lean_mkApp3(v_fst_437_, v___x_449_, v___x_449_, v_a_483_);
if (v_isShared_445_ == 0)
{
v___x_486_ = v___x_444_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_fst_441_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_snd_442_);
v___x_486_ = v_reuseFailAlloc_493_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_486_);
lean_ctor_set(v___x_439_, 0, v___x_484_);
v___x_488_ = v___x_439_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_486_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_488_);
lean_ctor_set(v___x_435_, 0, v___x_481_);
v___x_490_ = v___x_435_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
v_a_405_ = v___x_490_;
goto v___jp_404_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec_ref(v___x_481_);
lean_del_object(v___x_444_);
lean_dec(v_snd_442_);
lean_dec(v_fst_441_);
lean_del_object(v___x_439_);
lean_dec(v_fst_437_);
lean_del_object(v___x_435_);
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_494_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_482_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_del_object(v___x_444_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
goto v___jp_455_;
}
}
else
{
lean_del_object(v___x_444_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
goto v___jp_455_;
}
v___jp_455_:
{
if (v_nameSubgoals_392_ == 0)
{
lean_object* v___x_456_; 
lean_inc(v_origTag_393_);
lean_inc(v___x_449_);
v___x_456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_449_, v_fst_433_, v_fst_437_, v_fst_441_, v_snd_442_, v_origTag_393_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v___y_410_ = v___x_456_;
goto v___jp_409_;
}
else
{
lean_object* v___x_457_; 
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v_fst_437_);
v___x_457_ = lean_infer_type(v_fst_437_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
v___x_459_ = lean_whnf(v_a_458_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = l_Lean_Expr_bindingName_x21(v_a_460_);
lean_dec(v_a_460_);
lean_inc(v_origTag_393_);
v___x_462_ = l_Lean_Meta_appendTag(v_origTag_393_, v___x_461_);
lean_dec(v___x_461_);
lean_inc(v___x_449_);
v___x_463_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_449_, v_fst_433_, v_fst_437_, v_fst_441_, v_snd_442_, v___x_462_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v___y_410_ = v___x_463_;
goto v___jp_409_;
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_snd_442_);
lean_dec(v_fst_441_);
lean_dec(v_fst_437_);
lean_dec(v_fst_433_);
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_464_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_459_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_459_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_snd_442_);
lean_dec(v_fst_441_);
lean_dec(v_fst_437_);
lean_dec(v_fst_433_);
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_472_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_457_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_457_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_del_object(v___x_444_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
v___x_502_ = lean_box(0);
v___x_503_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_441_, v_snd_442_, v_fst_437_, v_fst_433_, v___x_502_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
v___y_410_ = v___x_503_;
goto v___jp_409_;
}
case 5:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_inc(v___x_449_);
v___x_504_ = l_Lean_Expr_app___override(v_fst_437_, v___x_449_);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc_ref(v___x_504_);
v___x_505_ = lean_infer_type(v___x_504_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
v___x_507_ = lean_whnf(v_a_506_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = l_Lean_Expr_bindingDomain_x21(v_a_508_);
lean_dec(v_a_508_);
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
v___x_511_ = 0;
v___x_512_ = lean_box(0);
v___x_513_ = l_Lean_Meta_mkFreshExprMVar(v___x_510_, v___x_511_, v___x_512_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc_n(v_a_514_, 3);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_Expr_app___override(v_fst_433_, v_a_514_);
v___x_516_ = l_Lean_Expr_app___override(v___x_504_, v_a_514_);
v___x_517_ = l_Lean_Expr_mvarId_x21(v_a_514_);
lean_dec(v_a_514_);
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
v___x_519_ = lean_array_push(v_snd_442_, v___x_518_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 1, v___x_519_);
v___x_521_ = v___x_444_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_fst_441_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_528_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_521_);
lean_ctor_set(v___x_439_, 0, v___x_516_);
v___x_523_ = v___x_439_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_523_);
lean_ctor_set(v___x_435_, 0, v___x_515_);
v___x_525_ = v___x_435_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
v_a_405_ = v___x_525_;
goto v___jp_404_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v___x_504_);
lean_del_object(v___x_444_);
lean_dec(v_snd_442_);
lean_dec(v_fst_441_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_529_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_513_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_513_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v___x_504_);
lean_del_object(v___x_444_);
lean_dec(v_snd_442_);
lean_dec(v_fst_441_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_537_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_507_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_507_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v___x_504_);
lean_del_object(v___x_444_);
lean_dec(v_snd_442_);
lean_dec(v_fst_441_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
lean_dec(v_fst_433_);
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_545_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_505_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_505_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
default: 
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_n(v___x_449_, 2);
v___x_553_ = l_Lean_Expr_app___override(v_fst_433_, v___x_449_);
v___x_554_ = l_Lean_Expr_app___override(v_fst_437_, v___x_449_);
if (v_addImplicitArgs_396_ == 0)
{
uint8_t v___x_567_; 
v___x_567_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_450_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_del_object(v___x_444_);
lean_del_object(v___x_439_);
lean_del_object(v___x_435_);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v_fst_441_);
lean_ctor_set(v___x_568_, 1, v_snd_442_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_554_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_553_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v_a_405_ = v___x_570_;
goto v___jp_404_;
}
else
{
goto v___jp_555_;
}
}
else
{
goto v___jp_555_;
}
v___jp_555_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_array_push(v_fst_441_, v___x_556_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_557_);
v___x_559_ = v___x_444_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_442_);
v___x_559_ = v_reuseFailAlloc_566_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_559_);
lean_ctor_set(v___x_439_, 0, v___x_554_);
v___x_561_ = v___x_439_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_559_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_561_);
lean_ctor_set(v___x_435_, 0, v___x_553_);
v___x_563_ = v___x_435_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
v_a_405_ = v___x_563_;
goto v___jp_404_;
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
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_nat_add(v_a_397_, v___x_406_);
lean_dec(v_a_397_);
v_a_397_ = v___x_407_;
v_b_398_ = v_a_405_;
goto _start;
}
v___jp_409_:
{
if (lean_obj_tag(v___y_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_420_; 
v_a_411_ = lean_ctor_get(v___y_410_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___y_410_);
if (v_isSharedCheck_420_ == 0)
{
v___x_413_ = v___y_410_;
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___y_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
if (lean_obj_tag(v_a_411_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; 
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_415_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v_a_411_, 1);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_a_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v_a_419_; 
lean_del_object(v___x_413_);
v_a_419_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v_a_411_, 1);
v_a_405_ = v_a_419_;
goto v___jp_404_;
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v_a_397_);
lean_dec(v_origTag_393_);
v_a_421_ = lean_ctor_get(v___y_410_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___y_410_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___y_410_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___y_410_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___boxed(lean_object* v_upperBound_576_, lean_object* v_args_577_, lean_object* v_nameSubgoals_578_, lean_object* v_origTag_579_, lean_object* v_a_580_, lean_object* v___x_581_, lean_object* v_addImplicitArgs_582_, lean_object* v_a_583_, lean_object* v_b_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v_nameSubgoals_boxed_590_; uint8_t v_addImplicitArgs_boxed_591_; lean_object* v_res_592_; 
v_nameSubgoals_boxed_590_ = lean_unbox(v_nameSubgoals_578_);
v_addImplicitArgs_boxed_591_ = lean_unbox(v_addImplicitArgs_582_);
v_res_592_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_576_, v_args_577_, v_nameSubgoals_boxed_590_, v_origTag_579_, v_a_580_, v___x_581_, v_addImplicitArgs_boxed_591_, v_a_583_, v_b_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec_ref(v___x_581_);
lean_dec_ref(v_a_580_);
lean_dec_ref(v_args_577_);
lean_dec(v_upperBound_576_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(lean_object* v_a_593_, lean_object* v_b_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_array_600_; lean_object* v_start_601_; lean_object* v_stop_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_617_; 
v_array_600_ = lean_ctor_get(v_a_593_, 0);
v_start_601_ = lean_ctor_get(v_a_593_, 1);
v_stop_602_ = lean_ctor_get(v_a_593_, 2);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_593_);
if (v_isSharedCheck_617_ == 0)
{
v___x_604_ = v_a_593_;
v_isShared_605_ = v_isSharedCheck_617_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_stop_602_);
lean_inc(v_start_601_);
lean_inc(v_array_600_);
lean_dec(v_a_593_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_617_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v___x_606_; 
v___x_606_ = lean_nat_dec_lt(v_start_601_, v_stop_602_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_del_object(v___x_604_);
lean_dec(v_stop_602_);
lean_dec(v_start_601_);
lean_dec_ref(v_array_600_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_b_594_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_array_fget_borrowed(v_array_600_, v_start_601_);
lean_inc(v___x_608_);
v___x_609_ = l_Lean_Meta_mkCongrFun(v_b_594_, v___x_608_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_start_601_, v___x_611_);
lean_dec(v_start_601_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_612_);
v___x_614_ = v___x_604_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_array_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_stop_602_);
v___x_614_ = v_reuseFailAlloc_616_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v_a_593_ = v___x_614_;
v_b_594_ = v_a_610_;
goto _start;
}
}
else
{
lean_del_object(v___x_604_);
lean_dec(v_stop_602_);
lean_dec(v_start_601_);
lean_dec_ref(v_array_600_);
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg___boxed(lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_618_, v_b_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(lean_object* v_origTag_633_, lean_object* v_f_634_, lean_object* v_args_635_, uint8_t v_addImplicitArgs_636_, uint8_t v_nameSubgoals_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_proof_644_; lean_object* v_mvarIdsNew_645_; lean_object* v_mvarIdsNewInsts_646_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_array_get_size(v_args_635_);
lean_inc_ref(v_f_634_);
v___x_651_ = l_Lean_Meta_getFunInfoNArgs(v_f_634_, v___x_650_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
lean_inc_ref(v_f_634_);
v___x_653_ = l_Lean_Meta_getCongrSimpKinds(v_f_634_, v_a_652_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; lean_object* v___x_656_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = 0;
lean_inc(v_a_652_);
lean_inc_ref(v_f_634_);
v___x_656_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_634_, v_a_652_, v_a_654_, v___x_655_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
if (lean_obj_tag(v_a_657_) == 1)
{
lean_object* v_val_658_; lean_object* v_proof_659_; lean_object* v_argKinds_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_val_658_ = lean_ctor_get(v_a_657_, 0);
lean_inc(v_val_658_);
lean_dec_ref_known(v_a_657_, 1);
v_proof_659_ = lean_ctor_get(v_val_658_, 1);
lean_inc_ref(v_proof_659_);
v_argKinds_660_ = lean_ctor_get(v_val_658_, 2);
lean_inc_ref(v_argKinds_660_);
lean_dec(v_val_658_);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_array_get_size(v_argKinds_660_);
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1));
v___x_664_ = lean_nat_dec_lt(v___x_662_, v___x_650_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_proof_659_);
lean_ctor_set(v___x_665_, 1, v___x_663_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_f_634_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_inc(v_origTag_633_);
v___x_667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v___x_662_, v_args_635_, v_nameSubgoals_637_, v_origTag_633_, v_a_652_, v_argKinds_660_, v_addImplicitArgs_636_, v___x_661_, v___x_666_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec_ref(v_argKinds_660_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v_snd_669_; lean_object* v_snd_670_; lean_object* v_fst_671_; lean_object* v_fst_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v_lower_680_; lean_object* v_upper_681_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v_snd_669_ = lean_ctor_get(v_a_668_, 1);
lean_inc(v_snd_669_);
v_snd_670_ = lean_ctor_get(v_snd_669_, 1);
lean_inc(v_snd_670_);
v_fst_671_ = lean_ctor_get(v_a_668_, 0);
lean_inc(v_fst_671_);
lean_dec(v_a_668_);
v_fst_672_ = lean_ctor_get(v_snd_669_, 0);
lean_inc(v_fst_672_);
lean_dec(v_snd_669_);
v_fst_673_ = lean_ctor_get(v_snd_670_, 0);
lean_inc(v_fst_673_);
v_snd_674_ = lean_ctor_get(v_snd_670_, 1);
lean_inc(v_snd_674_);
lean_dec(v_snd_670_);
if (v___x_664_ == 0)
{
lean_dec(v_fst_671_);
lean_dec(v_a_652_);
lean_dec_ref(v_args_635_);
lean_dec(v_origTag_633_);
v_proof_644_ = v_fst_672_;
v_mvarIdsNew_645_ = v_fst_673_;
v_mvarIdsNewInsts_646_ = v_snd_674_;
goto v___jp_643_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_eq(v___x_662_, v___x_661_);
if (v___x_719_ == 0)
{
v___y_713_ = v_a_638_;
v___y_714_ = v_a_639_;
v___y_715_ = v_a_640_;
v___y_716_ = v_a_641_;
goto v___jp_712_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_721_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_720_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_dec_ref_known(v___x_721_, 1);
v___y_713_ = v_a_638_;
v___y_714_ = v_a_639_;
v___y_715_ = v_a_640_;
v___y_716_ = v_a_641_;
goto v___jp_712_;
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_672_);
lean_dec(v_fst_671_);
lean_dec(v_a_652_);
lean_dec_ref(v_args_635_);
lean_dec(v_origTag_633_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
v___jp_675_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = l_Array_toSubarray___redArg(v_args_635_, v_lower_680_, v_upper_681_);
lean_inc_ref(v___x_682_);
v___x_683_ = l_Subarray_copy___redArg(v___x_682_);
v___x_684_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_633_, v_fst_671_, v___x_683_, v_addImplicitArgs_636_, v_nameSubgoals_637_, v___y_678_, v___y_676_, v___y_677_, v___y_679_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v_snd_686_; lean_object* v_fst_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_690_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v_snd_686_ = lean_ctor_get(v_a_685_, 1);
lean_inc(v_snd_686_);
v_fst_687_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_fst_687_);
lean_dec(v_a_685_);
v_fst_688_ = lean_ctor_get(v_snd_686_, 0);
lean_inc(v_fst_688_);
v_snd_689_ = lean_ctor_get(v_snd_686_, 1);
lean_inc(v_snd_689_);
lean_dec(v_snd_686_);
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_682_, v_fst_672_, v___y_678_, v___y_676_, v___y_677_, v___y_679_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_mkEqTrans(v_a_691_, v_fst_687_, v___y_678_, v___y_676_, v___y_677_, v___y_679_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = l_Array_append___redArg(v_fst_673_, v_fst_688_);
lean_dec(v_fst_688_);
v___x_695_ = l_Array_append___redArg(v_snd_674_, v_snd_689_);
lean_dec(v_snd_689_);
v_proof_644_ = v_a_693_;
v_mvarIdsNew_645_ = v___x_694_;
v_mvarIdsNewInsts_646_ = v___x_695_;
goto v___jp_643_;
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_snd_689_);
lean_dec(v_fst_688_);
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
v_a_696_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_692_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_snd_689_);
lean_dec(v_fst_688_);
lean_dec(v_fst_687_);
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
v_a_704_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_690_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_690_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_dec_ref(v___x_682_);
lean_dec(v_snd_674_);
lean_dec(v_fst_673_);
lean_dec(v_fst_672_);
return v___x_684_;
}
}
v___jp_712_:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = l_Lean_Meta_FunInfo_getArity(v_a_652_);
lean_dec(v_a_652_);
v___x_718_ = lean_nat_dec_le(v___x_717_, v___x_661_);
if (v___x_718_ == 0)
{
v___y_676_ = v___y_714_;
v___y_677_ = v___y_715_;
v___y_678_ = v___y_713_;
v___y_679_ = v___y_716_;
v_lower_680_ = v___x_717_;
v_upper_681_ = v___x_650_;
goto v___jp_675_;
}
else
{
lean_dec(v___x_717_);
v___y_676_ = v___y_714_;
v___y_677_ = v___y_715_;
v___y_678_ = v___y_713_;
v___y_679_ = v___y_716_;
v_lower_680_ = v___x_661_;
v_upper_681_ = v___x_650_;
goto v___jp_675_;
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_a_652_);
lean_dec_ref(v_args_635_);
lean_dec(v_origTag_633_);
v_a_730_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_667_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_667_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
lean_dec(v_a_657_);
lean_dec(v_a_652_);
lean_dec_ref(v_args_635_);
lean_dec_ref(v_f_634_);
lean_dec(v_origTag_633_);
v___x_738_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_739_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_738_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_739_;
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_a_652_);
lean_dec_ref(v_args_635_);
lean_dec_ref(v_f_634_);
lean_dec(v_origTag_633_);
v_a_740_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_656_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_656_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_a_652_);
lean_dec_ref(v_args_635_);
lean_dec_ref(v_f_634_);
lean_dec(v_origTag_633_);
v_a_748_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_653_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_653_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_args_635_);
lean_dec_ref(v_f_634_);
lean_dec(v_origTag_633_);
v_a_756_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_651_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_651_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
v___jp_643_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v_mvarIdsNew_645_);
lean_ctor_set(v___x_647_, 1, v_mvarIdsNewInsts_646_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_proof_644_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___boxed(lean_object* v_origTag_764_, lean_object* v_f_765_, lean_object* v_args_766_, lean_object* v_addImplicitArgs_767_, lean_object* v_nameSubgoals_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
uint8_t v_addImplicitArgs_boxed_774_; uint8_t v_nameSubgoals_boxed_775_; lean_object* v_res_776_; 
v_addImplicitArgs_boxed_774_ = lean_unbox(v_addImplicitArgs_767_);
v_nameSubgoals_boxed_775_ = lean_unbox(v_nameSubgoals_768_);
v_res_776_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_764_, v_f_765_, v_args_766_, v_addImplicitArgs_boxed_774_, v_nameSubgoals_boxed_775_, v_a_769_, v_a_770_, v_a_771_, v_a_772_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_object* v_inst_777_, lean_object* v_R_778_, lean_object* v_a_779_, lean_object* v_b_780_, lean_object* v_c_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_779_, v_b_780_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___boxed(lean_object* v_inst_788_, lean_object* v_R_789_, lean_object* v_a_790_, lean_object* v_b_791_, lean_object* v_c_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(v_inst_788_, v_R_789_, v_a_790_, v_b_791_, v_c_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(lean_object* v_upperBound_799_, lean_object* v_args_800_, uint8_t v_nameSubgoals_801_, lean_object* v_origTag_802_, lean_object* v_a_803_, lean_object* v___x_804_, uint8_t v_addImplicitArgs_805_, lean_object* v_inst_806_, lean_object* v_R_807_, lean_object* v_a_808_, lean_object* v_b_809_, lean_object* v_c_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_799_, v_args_800_, v_nameSubgoals_801_, v_origTag_802_, v_a_803_, v___x_804_, v_addImplicitArgs_805_, v_a_808_, v_b_809_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_817_ = _args[0];
lean_object* v_args_818_ = _args[1];
lean_object* v_nameSubgoals_819_ = _args[2];
lean_object* v_origTag_820_ = _args[3];
lean_object* v_a_821_ = _args[4];
lean_object* v___x_822_ = _args[5];
lean_object* v_addImplicitArgs_823_ = _args[6];
lean_object* v_inst_824_ = _args[7];
lean_object* v_R_825_ = _args[8];
lean_object* v_a_826_ = _args[9];
lean_object* v_b_827_ = _args[10];
lean_object* v_c_828_ = _args[11];
lean_object* v___y_829_ = _args[12];
lean_object* v___y_830_ = _args[13];
lean_object* v___y_831_ = _args[14];
lean_object* v___y_832_ = _args[15];
lean_object* v___y_833_ = _args[16];
_start:
{
uint8_t v_nameSubgoals_boxed_834_; uint8_t v_addImplicitArgs_boxed_835_; lean_object* v_res_836_; 
v_nameSubgoals_boxed_834_ = lean_unbox(v_nameSubgoals_819_);
v_addImplicitArgs_boxed_835_ = lean_unbox(v_addImplicitArgs_823_);
v_res_836_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(v_upperBound_817_, v_args_818_, v_nameSubgoals_boxed_834_, v_origTag_820_, v_a_821_, v___x_822_, v_addImplicitArgs_boxed_835_, v_inst_824_, v_R_825_, v_a_826_, v_b_827_, v_c_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v___x_822_);
lean_dec_ref(v_a_821_);
lean_dec_ref(v_args_818_);
lean_dec(v_upperBound_817_);
return v_res_836_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(lean_object* v_tacticName_846_, lean_object* v_rhs_847_, lean_object* v_rhs_x27_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
lean_inc_ref(v_rhs_x27_848_);
lean_inc_ref(v_rhs_847_);
v___x_854_ = l_Lean_Meta_isExprDefEqGuarded(v_rhs_847_, v_rhs_x27_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_876_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_876_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_876_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_876_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
uint8_t v___x_859_; 
v___x_859_ = lean_unbox(v_a_855_);
lean_dec(v_a_855_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_del_object(v___x_857_);
v___x_860_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_861_ = l_Lean_stringToMessageData(v_tacticName_846_);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_indentExpr(v_rhs_847_);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_indentExpr(v_rhs_x27_848_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_870_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_874_; 
lean_dec_ref(v_rhs_x27_848_);
lean_dec_ref(v_rhs_847_);
lean_dec_ref(v_tacticName_846_);
v___x_872_ = lean_box(0);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_872_);
v___x_874_ = v___x_857_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v_rhs_x27_848_);
lean_dec_ref(v_rhs_847_);
lean_dec_ref(v_tacticName_846_);
v_a_877_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_854_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_854_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___boxed(lean_object* v_tacticName_885_, lean_object* v_rhs_886_, lean_object* v_rhs_x27_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_885_, v_rhs_886_, v_rhs_x27_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_893_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2));
v___x_899_ = l_Lean_stringToMessageData(v___x_898_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(lean_object* v_tacticName_903_, lean_object* v_rhs_904_, lean_object* v_proof_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; 
lean_inc(v_a_909_);
lean_inc_ref(v_a_908_);
lean_inc(v_a_907_);
lean_inc_ref(v_a_906_);
v___x_911_ = lean_infer_type(v_proof_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
lean_inc(v_a_909_);
lean_inc_ref(v_a_908_);
lean_inc(v_a_907_);
lean_inc_ref(v_a_906_);
v___x_913_ = lean_whnf(v_a_912_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1));
v___x_916_ = lean_unsigned_to_nat(3u);
v___x_917_ = l_Lean_Expr_isAppOfArity(v_a_914_, v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v_a_914_);
lean_dec_ref(v_rhs_904_);
v___x_918_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_919_ = l_Lean_stringToMessageData(v_tacticName_903_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_922_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = l_Lean_Expr_appArg_x21(v_a_914_);
lean_dec(v_a_914_);
v___x_925_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_903_, v_rhs_904_, v___x_924_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
return v___x_925_;
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_rhs_904_);
lean_dec_ref(v_tacticName_903_);
v_a_926_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_913_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_913_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_rhs_904_);
lean_dec_ref(v_tacticName_903_);
v_a_934_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_911_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_911_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___boxed(lean_object* v_tacticName_942_, lean_object* v_rhs_943_, lean_object* v_proof_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_942_, v_rhs_943_, v_proof_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(lean_object* v_e_951_, lean_object* v___y_952_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_Expr_hasMVar(v_e_951_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_e_951_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v_mctx_957_; lean_object* v___x_958_; lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_961_; lean_object* v_cache_962_; lean_object* v_zetaDeltaFVarIds_963_; lean_object* v_postponed_964_; lean_object* v_diag_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_974_; 
v___x_956_ = lean_st_ref_get(v___y_952_);
v_mctx_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc_ref(v_mctx_957_);
lean_dec(v___x_956_);
v___x_958_ = l_Lean_instantiateMVarsCore(v_mctx_957_, v_e_951_);
v_fst_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_fst_959_);
v_snd_960_ = lean_ctor_get(v___x_958_, 1);
lean_inc(v_snd_960_);
lean_dec_ref(v___x_958_);
v___x_961_ = lean_st_ref_take(v___y_952_);
v_cache_962_ = lean_ctor_get(v___x_961_, 1);
v_zetaDeltaFVarIds_963_ = lean_ctor_get(v___x_961_, 2);
v_postponed_964_ = lean_ctor_get(v___x_961_, 3);
v_diag_965_ = lean_ctor_get(v___x_961_, 4);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v___x_961_, 0);
lean_dec(v_unused_975_);
v___x_967_ = v___x_961_;
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_diag_965_);
lean_inc(v_postponed_964_);
lean_inc(v_zetaDeltaFVarIds_963_);
lean_inc(v_cache_962_);
lean_dec(v___x_961_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v_snd_960_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_snd_960_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_cache_962_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_zetaDeltaFVarIds_963_);
lean_ctor_set(v_reuseFailAlloc_973_, 3, v_postponed_964_);
lean_ctor_set(v_reuseFailAlloc_973_, 4, v_diag_965_);
v___x_970_ = v_reuseFailAlloc_973_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_st_ref_put(v___y_952_, v___x_970_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v_fst_959_);
return v___x_972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg___boxed(lean_object* v_e_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_976_, v___y_977_);
lean_dec(v___y_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(lean_object* v_e_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_980_, v___y_982_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___boxed(lean_object* v_e_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(v_e_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(lean_object* v_mvarId_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_994_, v_x_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1001_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1001_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg___boxed(lean_object* v_mvarId_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_object* v_00_u03b1_1026_, lean_object* v_mvarId_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1027_, v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_mvarId_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(v_00_u03b1_1035_, v_mvarId_1036_, v_x_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
if (lean_obj_tag(v_a_1044_) == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = l_List_reverse___redArg(v_a_1045_);
return v___x_1046_;
}
else
{
lean_object* v_head_1047_; lean_object* v_tail_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1057_; 
v_head_1047_ = lean_ctor_get(v_a_1044_, 0);
v_tail_1048_ = lean_ctor_get(v_a_1044_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_a_1044_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1050_ = v_a_1044_;
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_tail_1048_);
lean_inc(v_head_1047_);
lean_dec(v_a_1044_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1057_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v_head_1047_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_a_1045_);
lean_ctor_set(v___x_1050_, 0, v___x_1052_);
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_a_1045_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
v_a_1044_ = v_tail_1048_;
v_a_1045_ = v___x_1054_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v_ks_1062_; lean_object* v_vs_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1087_; 
v_ks_1062_ = lean_ctor_get(v_x_1058_, 0);
v_vs_1063_ = lean_ctor_get(v_x_1058_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_x_1058_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1065_ = v_x_1058_;
v_isShared_1066_ = v_isSharedCheck_1087_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_vs_1063_);
lean_inc(v_ks_1062_);
lean_dec(v_x_1058_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1087_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_array_get_size(v_ks_1062_);
v___x_1068_ = lean_nat_dec_lt(v_x_1059_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_dec(v_x_1059_);
v___x_1069_ = lean_array_push(v_ks_1062_, v_x_1060_);
v___x_1070_ = lean_array_push(v_vs_1063_, v_x_1061_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1070_);
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1072_ = v___x_1065_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
lean_object* v_k_x27_1074_; uint8_t v___x_1075_; 
v_k_x27_1074_ = lean_array_fget_borrowed(v_ks_1062_, v_x_1059_);
v___x_1075_ = l_Lean_instBEqMVarId_beq(v_x_1060_, v_k_x27_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1077_; 
if (v_isShared_1066_ == 0)
{
v___x_1077_ = v___x_1065_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_ks_1062_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_vs_1063_);
v___x_1077_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_x_1059_, v___x_1078_);
lean_dec(v_x_1059_);
v_x_1058_ = v___x_1077_;
v_x_1059_ = v___x_1079_;
goto _start;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1082_ = lean_array_fset(v_ks_1062_, v_x_1059_, v_x_1060_);
v___x_1083_ = lean_array_fset(v_vs_1063_, v_x_1059_, v_x_1061_);
lean_dec(v_x_1059_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1083_);
lean_ctor_set(v___x_1065_, 0, v___x_1082_);
v___x_1085_ = v___x_1065_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_n_1088_, lean_object* v_k_1089_, lean_object* v_v_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_n_1088_, v___x_1091_, v_k_1089_, v_v_1090_);
return v___x_1092_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1094_, size_t v_x_1095_, size_t v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 0)
{
lean_object* v_es_1099_; size_t v___x_1100_; size_t v___x_1101_; lean_object* v_j_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_es_1099_ = lean_ctor_get(v_x_1094_, 0);
v___x_1100_ = ((size_t)31ULL);
v___x_1101_ = lean_usize_land(v_x_1095_, v___x_1100_);
v_j_1102_ = lean_usize_to_nat(v___x_1101_);
v___x_1103_ = lean_array_get_size(v_es_1099_);
v___x_1104_ = lean_nat_dec_lt(v_j_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec(v_j_1102_);
lean_dec(v_x_1098_);
lean_dec(v_x_1097_);
return v_x_1094_;
}
else
{
lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1143_; 
lean_inc_ref(v_es_1099_);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1094_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v_x_1094_, 0);
lean_dec(v_unused_1144_);
v___x_1106_ = v_x_1094_;
v_isShared_1107_ = v_isSharedCheck_1143_;
goto v_resetjp_1105_;
}
else
{
lean_dec(v_x_1094_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1143_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_v_1108_; lean_object* v___x_1109_; lean_object* v_xs_x27_1110_; lean_object* v___y_1112_; 
v_v_1108_ = lean_array_fget(v_es_1099_, v_j_1102_);
v___x_1109_ = lean_box(0);
v_xs_x27_1110_ = lean_array_fset(v_es_1099_, v_j_1102_, v___x_1109_);
switch(lean_obj_tag(v_v_1108_))
{
case 0:
{
lean_object* v_key_1117_; lean_object* v_val_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1128_; 
v_key_1117_ = lean_ctor_get(v_v_1108_, 0);
v_val_1118_ = lean_ctor_get(v_v_1108_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_v_1108_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1120_ = v_v_1108_;
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_val_1118_);
lean_inc(v_key_1117_);
lean_dec(v_v_1108_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; 
v___x_1122_ = l_Lean_instBEqMVarId_beq(v_x_1097_, v_key_1117_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_del_object(v___x_1120_);
v___x_1123_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1117_, v_val_1118_, v_x_1097_, v_x_1098_);
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
v___y_1112_ = v___x_1124_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1126_; 
lean_dec(v_val_1118_);
lean_dec(v_key_1117_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v_x_1098_);
lean_ctor_set(v___x_1120_, 0, v_x_1097_);
v___x_1126_ = v___x_1120_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_x_1097_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_x_1098_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
v___y_1112_ = v___x_1126_;
goto v___jp_1111_;
}
}
}
}
case 1:
{
lean_object* v_node_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1141_; 
v_node_1129_ = lean_ctor_get(v_v_1108_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_v_1108_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1131_ = v_v_1108_;
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_node_1129_);
lean_dec(v_v_1108_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1141_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; size_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1133_ = ((size_t)5ULL);
v___x_1134_ = lean_usize_shift_right(v_x_1095_, v___x_1133_);
v___x_1135_ = ((size_t)1ULL);
v___x_1136_ = lean_usize_add(v_x_1096_, v___x_1135_);
v___x_1137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_node_1129_, v___x_1134_, v___x_1136_, v_x_1097_, v_x_1098_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1137_);
v___x_1139_ = v___x_1131_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
v___y_1112_ = v___x_1139_;
goto v___jp_1111_;
}
}
}
default: 
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_x_1097_);
lean_ctor_set(v___x_1142_, 1, v_x_1098_);
v___y_1112_ = v___x_1142_;
goto v___jp_1111_;
}
}
v___jp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1113_ = lean_array_fset(v_xs_x27_1110_, v_j_1102_, v___y_1112_);
lean_dec(v_j_1102_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1113_);
v___x_1115_ = v___x_1106_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
else
{
lean_object* v_ks_1145_; lean_object* v_vs_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1166_; 
v_ks_1145_ = lean_ctor_get(v_x_1094_, 0);
v_vs_1146_ = lean_ctor_get(v_x_1094_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1094_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1148_ = v_x_1094_;
v_isShared_1149_ = v_isSharedCheck_1166_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_vs_1146_);
lean_inc(v_ks_1145_);
lean_dec(v_x_1094_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1166_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_ks_1145_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_vs_1146_);
v___x_1151_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v_newNode_1152_; uint8_t v___y_1154_; size_t v___x_1160_; uint8_t v___x_1161_; 
v_newNode_1152_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v___x_1151_, v_x_1097_, v_x_1098_);
v___x_1160_ = ((size_t)7ULL);
v___x_1161_ = lean_usize_dec_le(v___x_1160_, v_x_1096_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1152_);
v___x_1163_ = lean_unsigned_to_nat(4u);
v___x_1164_ = lean_nat_dec_lt(v___x_1162_, v___x_1163_);
lean_dec(v___x_1162_);
v___y_1154_ = v___x_1164_;
goto v___jp_1153_;
}
else
{
v___y_1154_ = v___x_1161_;
goto v___jp_1153_;
}
v___jp_1153_:
{
if (v___y_1154_ == 0)
{
lean_object* v_ks_1155_; lean_object* v_vs_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_ks_1155_ = lean_ctor_get(v_newNode_1152_, 0);
lean_inc_ref(v_ks_1155_);
v_vs_1156_ = lean_ctor_get(v_newNode_1152_, 1);
lean_inc_ref(v_vs_1156_);
lean_dec_ref(v_newNode_1152_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_x_1096_, v_ks_1155_, v_vs_1156_, v___x_1157_, v___x_1158_);
lean_dec_ref(v_vs_1156_);
lean_dec_ref(v_ks_1155_);
return v___x_1159_;
}
else
{
return v_newNode_1152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(size_t v_depth_1167_, lean_object* v_keys_1168_, lean_object* v_vals_1169_, lean_object* v_i_1170_, lean_object* v_entries_1171_){
_start:
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_array_get_size(v_keys_1168_);
v___x_1173_ = lean_nat_dec_lt(v_i_1170_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v_i_1170_);
return v_entries_1171_;
}
else
{
lean_object* v_k_1174_; lean_object* v_v_1175_; uint64_t v___x_1176_; size_t v_h_1177_; size_t v___x_1178_; lean_object* v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v_h_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_k_1174_ = lean_array_fget_borrowed(v_keys_1168_, v_i_1170_);
v_v_1175_ = lean_array_fget_borrowed(v_vals_1169_, v_i_1170_);
v___x_1176_ = l_Lean_instHashableMVarId_hash(v_k_1174_);
v_h_1177_ = lean_uint64_to_usize(v___x_1176_);
v___x_1178_ = ((size_t)5ULL);
v___x_1179_ = lean_unsigned_to_nat(1u);
v___x_1180_ = ((size_t)1ULL);
v___x_1181_ = lean_usize_sub(v_depth_1167_, v___x_1180_);
v___x_1182_ = lean_usize_mul(v___x_1178_, v___x_1181_);
v_h_1183_ = lean_usize_shift_right(v_h_1177_, v___x_1182_);
v___x_1184_ = lean_nat_add(v_i_1170_, v___x_1179_);
lean_dec(v_i_1170_);
lean_inc(v_v_1175_);
lean_inc(v_k_1174_);
v___x_1185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_entries_1171_, v_h_1183_, v_depth_1167_, v_k_1174_, v_v_1175_);
v_i_1170_ = v___x_1184_;
v_entries_1171_ = v___x_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1187_, lean_object* v_keys_1188_, lean_object* v_vals_1189_, lean_object* v_i_1190_, lean_object* v_entries_1191_){
_start:
{
size_t v_depth_boxed_1192_; lean_object* v_res_1193_; 
v_depth_boxed_1192_ = lean_unbox_usize(v_depth_1187_);
lean_dec(v_depth_1187_);
v_res_1193_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_boxed_1192_, v_keys_1188_, v_vals_1189_, v_i_1190_, v_entries_1191_);
lean_dec_ref(v_vals_1189_);
lean_dec_ref(v_keys_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_){
_start:
{
size_t v_x_3124__boxed_1199_; size_t v_x_3125__boxed_1200_; lean_object* v_res_1201_; 
v_x_3124__boxed_1199_ = lean_unbox_usize(v_x_1195_);
lean_dec(v_x_1195_);
v_x_3125__boxed_1200_ = lean_unbox_usize(v_x_1196_);
lean_dec(v_x_1196_);
v_res_1201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1194_, v_x_3124__boxed_1199_, v_x_3125__boxed_1200_, v_x_1197_, v_x_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
uint64_t v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = l_Lean_instHashableMVarId_hash(v_x_1203_);
v___x_1206_ = lean_uint64_to_usize(v___x_1205_);
v___x_1207_ = ((size_t)1ULL);
v___x_1208_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1202_, v___x_1206_, v___x_1207_, v_x_1203_, v_x_1204_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(lean_object* v_mvarId_1209_, lean_object* v_val_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v_mctx_1214_; lean_object* v_cache_1215_; lean_object* v_zetaDeltaFVarIds_1216_; lean_object* v_postponed_1217_; lean_object* v_diag_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1247_; 
v___x_1213_ = lean_st_ref_take(v___y_1211_);
v_mctx_1214_ = lean_ctor_get(v___x_1213_, 0);
v_cache_1215_ = lean_ctor_get(v___x_1213_, 1);
v_zetaDeltaFVarIds_1216_ = lean_ctor_get(v___x_1213_, 2);
v_postponed_1217_ = lean_ctor_get(v___x_1213_, 3);
v_diag_1218_ = lean_ctor_get(v___x_1213_, 4);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1220_ = v___x_1213_;
v_isShared_1221_ = v_isSharedCheck_1247_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_diag_1218_);
lean_inc(v_postponed_1217_);
lean_inc(v_zetaDeltaFVarIds_1216_);
lean_inc(v_cache_1215_);
lean_inc(v_mctx_1214_);
lean_dec(v___x_1213_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1247_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_depth_1222_; lean_object* v_levelAssignDepth_1223_; lean_object* v_lmvarCounter_1224_; lean_object* v_mvarCounter_1225_; lean_object* v_lDecls_1226_; lean_object* v_decls_1227_; lean_object* v_userNames_1228_; lean_object* v_lAssignment_1229_; lean_object* v_eAssignment_1230_; lean_object* v_dAssignment_1231_; lean_object* v_instanceTypedMVars_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1246_; 
v_depth_1222_ = lean_ctor_get(v_mctx_1214_, 0);
v_levelAssignDepth_1223_ = lean_ctor_get(v_mctx_1214_, 1);
v_lmvarCounter_1224_ = lean_ctor_get(v_mctx_1214_, 2);
v_mvarCounter_1225_ = lean_ctor_get(v_mctx_1214_, 3);
v_lDecls_1226_ = lean_ctor_get(v_mctx_1214_, 4);
v_decls_1227_ = lean_ctor_get(v_mctx_1214_, 5);
v_userNames_1228_ = lean_ctor_get(v_mctx_1214_, 6);
v_lAssignment_1229_ = lean_ctor_get(v_mctx_1214_, 7);
v_eAssignment_1230_ = lean_ctor_get(v_mctx_1214_, 8);
v_dAssignment_1231_ = lean_ctor_get(v_mctx_1214_, 9);
v_instanceTypedMVars_1232_ = lean_ctor_get(v_mctx_1214_, 10);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_mctx_1214_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1234_ = v_mctx_1214_;
v_isShared_1235_ = v_isSharedCheck_1246_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_instanceTypedMVars_1232_);
lean_inc(v_dAssignment_1231_);
lean_inc(v_eAssignment_1230_);
lean_inc(v_lAssignment_1229_);
lean_inc(v_userNames_1228_);
lean_inc(v_decls_1227_);
lean_inc(v_lDecls_1226_);
lean_inc(v_mvarCounter_1225_);
lean_inc(v_lmvarCounter_1224_);
lean_inc(v_levelAssignDepth_1223_);
lean_inc(v_depth_1222_);
lean_dec(v_mctx_1214_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1246_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_1230_, v_mvarId_1209_, v_val_1210_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 8, v___x_1236_);
v___x_1238_ = v___x_1234_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_depth_1222_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_levelAssignDepth_1223_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_lmvarCounter_1224_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_mvarCounter_1225_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_lDecls_1226_);
lean_ctor_set(v_reuseFailAlloc_1245_, 5, v_decls_1227_);
lean_ctor_set(v_reuseFailAlloc_1245_, 6, v_userNames_1228_);
lean_ctor_set(v_reuseFailAlloc_1245_, 7, v_lAssignment_1229_);
lean_ctor_set(v_reuseFailAlloc_1245_, 8, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1245_, 9, v_dAssignment_1231_);
lean_ctor_set(v_reuseFailAlloc_1245_, 10, v_instanceTypedMVars_1232_);
v___x_1238_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1240_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1238_);
v___x_1240_ = v___x_1220_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_cache_1215_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_zetaDeltaFVarIds_1216_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_postponed_1217_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_diag_1218_);
v___x_1240_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_st_ref_put(v___y_1211_, v___x_1240_);
v___x_1242_ = lean_box(0);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg___boxed(lean_object* v_mvarId_1248_, lean_object* v_val_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1248_, v_val_1249_, v___y_1250_);
lean_dec(v___y_1250_);
return v_res_1252_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1256_; lean_object* v_dummy_1257_; 
v___x_1256_ = lean_box(0);
v_dummy_1257_ = l_Lean_Expr_sort___override(v___x_1256_);
return v_dummy_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0(lean_object* v_mvarId_1259_, uint8_t v_addImplicitArgs_1260_, uint8_t v_nameSubgoals_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v___x_1267_; 
lean_inc(v_mvarId_1259_);
v___x_1267_ = l_Lean_MVarId_getTag(v_mvarId_1259_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
lean_inc(v_mvarId_1259_);
v___x_1269_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1259_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1359_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v_fst_1271_ = lean_ctor_get(v_a_1270_, 0);
v_snd_1272_ = lean_ctor_get(v_a_1270_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_a_1270_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1274_ = v_a_1270_;
v_isShared_1275_ = v_isSharedCheck_1359_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_snd_1272_);
lean_inc(v_fst_1271_);
lean_dec(v_a_1270_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1359_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1276_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1271_, v___y_1263_);
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = l_Lean_Expr_cleanupAnnotations(v_a_1277_);
v___x_1279_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v___x_1278_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; uint8_t v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_unbox(v_a_1280_);
lean_dec(v_a_1280_);
if (v___x_1281_ == 0)
{
uint8_t v___x_1282_; 
v___x_1282_ = l_Lean_Expr_isApp(v___x_1278_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
lean_dec(v_snd_1272_);
lean_dec(v_a_1268_);
lean_dec(v_mvarId_1259_);
v___x_1283_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1);
v___x_1284_ = l_Lean_indentExpr(v___x_1278_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set_tag(v___x_1274_, 7);
lean_ctor_set(v___x_1274_, 1, v___x_1284_);
lean_ctor_set(v___x_1274_, 0, v___x_1283_);
v___x_1286_ = v___x_1274_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1286_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1289_; lean_object* v_dummy_1290_; lean_object* v_nargs_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_del_object(v___x_1274_);
v___x_1289_ = l_Lean_Expr_getAppFn(v___x_1278_);
v_dummy_1290_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1291_ = l_Lean_Expr_getAppNumArgs(v___x_1278_);
lean_inc(v_nargs_1291_);
v___x_1292_ = lean_mk_array(v_nargs_1291_, v_dummy_1290_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_nat_sub(v_nargs_1291_, v___x_1293_);
lean_dec(v_nargs_1291_);
v___x_1295_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1278_, v___x_1292_, v___x_1294_);
v___x_1296_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_a_1268_, v___x_1289_, v___x_1295_, v_addImplicitArgs_1260_, v_nameSubgoals_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v_snd_1298_; lean_object* v_fst_1299_; lean_object* v_fst_1300_; lean_object* v_snd_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v_snd_1298_ = lean_ctor_get(v_a_1297_, 1);
lean_inc(v_snd_1298_);
v_fst_1299_ = lean_ctor_get(v_a_1297_, 0);
lean_inc_n(v_fst_1299_, 2);
lean_dec(v_a_1297_);
v_fst_1300_ = lean_ctor_get(v_snd_1298_, 0);
lean_inc(v_fst_1300_);
v_snd_1301_ = lean_ctor_get(v_snd_1298_, 1);
lean_inc(v_snd_1301_);
lean_dec(v_snd_1298_);
v___x_1302_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3));
v___x_1303_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v___x_1302_, v_snd_1272_, v_fst_1299_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref_known(v___x_1303_, 1);
v___x_1304_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1259_, v_fst_1299_, v___y_1263_);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1304_, 0);
lean_dec(v_unused_1315_);
v___x_1306_ = v___x_1304_;
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v___x_1304_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1314_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1308_ = lean_array_to_list(v_fst_1300_);
v___x_1309_ = lean_array_to_list(v_snd_1301_);
v___x_1310_ = l_List_appendTR___redArg(v___x_1308_, v___x_1309_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1310_);
v___x_1312_ = v___x_1306_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_snd_1301_);
lean_dec(v_fst_1300_);
lean_dec(v_fst_1299_);
lean_dec(v_mvarId_1259_);
v_a_1316_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1303_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1303_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_snd_1272_);
lean_dec(v_mvarId_1259_);
v_a_1324_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1296_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1296_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_object* v___x_1332_; 
lean_dec_ref(v___x_1278_);
lean_del_object(v___x_1274_);
lean_dec(v_snd_1272_);
lean_dec(v_a_1268_);
v___x_1332_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_1259_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1342_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(v_a_1333_, v___x_1337_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1338_);
v___x_1340_ = v___x_1335_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1332_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1332_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v___x_1278_);
lean_del_object(v___x_1274_);
lean_dec(v_snd_1272_);
lean_dec(v_a_1268_);
lean_dec(v_mvarId_1259_);
v_a_1351_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1279_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1279_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1268_);
lean_dec(v_mvarId_1259_);
v_a_1360_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1269_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1269_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_mvarId_1259_);
v_a_1368_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1267_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1267_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed(lean_object* v_mvarId_1376_, lean_object* v_addImplicitArgs_1377_, lean_object* v_nameSubgoals_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1384_; uint8_t v_nameSubgoals_boxed_1385_; lean_object* v_res_1386_; 
v_addImplicitArgs_boxed_1384_ = lean_unbox(v_addImplicitArgs_1377_);
v_nameSubgoals_boxed_1385_ = lean_unbox(v_nameSubgoals_1378_);
v_res_1386_ = l_Lean_Elab_Tactic_Conv_congr___lam__0(v_mvarId_1376_, v_addImplicitArgs_boxed_1384_, v_nameSubgoals_boxed_1385_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr(lean_object* v_mvarId_1387_, uint8_t v_addImplicitArgs_1388_, uint8_t v_nameSubgoals_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; lean_object* v___x_1398_; 
v___x_1395_ = lean_box(v_addImplicitArgs_1388_);
v___x_1396_ = lean_box(v_nameSubgoals_1389_);
lean_inc(v_mvarId_1387_);
v___f_1397_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1397_, 0, v_mvarId_1387_);
lean_closure_set(v___f_1397_, 1, v___x_1395_);
lean_closure_set(v___f_1397_, 2, v___x_1396_);
v___x_1398_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1387_, v___f_1397_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___boxed(lean_object* v_mvarId_1399_, lean_object* v_addImplicitArgs_1400_, lean_object* v_nameSubgoals_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1407_; uint8_t v_nameSubgoals_boxed_1408_; lean_object* v_res_1409_; 
v_addImplicitArgs_boxed_1407_ = lean_unbox(v_addImplicitArgs_1400_);
v_nameSubgoals_boxed_1408_ = lean_unbox(v_nameSubgoals_1401_);
v_res_1409_ = l_Lean_Elab_Tactic_Conv_congr(v_mvarId_1399_, v_addImplicitArgs_boxed_1407_, v_nameSubgoals_boxed_1408_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(lean_object* v_mvarId_1410_, lean_object* v_val_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1410_, v_val_1411_, v___y_1413_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___boxed(lean_object* v_mvarId_1418_, lean_object* v_val_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(v_mvarId_1418_, v_val_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_x_1427_, v_x_1428_, v_x_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1431_, lean_object* v_x_1432_, size_t v_x_1433_, size_t v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1432_, v_x_1433_, v_x_1434_, v_x_1435_, v_x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
size_t v_x_3622__boxed_1444_; size_t v_x_3623__boxed_1445_; lean_object* v_res_1446_; 
v_x_3622__boxed_1444_ = lean_unbox_usize(v_x_1440_);
lean_dec(v_x_1440_);
v_x_3623__boxed_1445_ = lean_unbox_usize(v_x_1441_);
lean_dec(v_x_1441_);
v_res_1446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(v_00_u03b2_1438_, v_x_1439_, v_x_3622__boxed_1444_, v_x_3623__boxed_1445_, v_x_1442_, v_x_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1447_, lean_object* v_n_1448_, lean_object* v_k_1449_, lean_object* v_v_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v_n_1448_, v_k_1449_, v_v_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1452_, size_t v_depth_1453_, lean_object* v_keys_1454_, lean_object* v_vals_1455_, lean_object* v_heq_1456_, lean_object* v_i_1457_, lean_object* v_entries_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_1453_, v_keys_1454_, v_vals_1455_, v_i_1457_, v_entries_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1460_, lean_object* v_depth_1461_, lean_object* v_keys_1462_, lean_object* v_vals_1463_, lean_object* v_heq_1464_, lean_object* v_i_1465_, lean_object* v_entries_1466_){
_start:
{
size_t v_depth_boxed_1467_; lean_object* v_res_1468_; 
v_depth_boxed_1467_ = lean_unbox_usize(v_depth_1461_);
lean_dec(v_depth_1461_);
v_res_1468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(v_00_u03b2_1460_, v_depth_boxed_1467_, v_keys_1462_, v_vals_1463_, v_heq_1464_, v_i_1465_, v_entries_1466_);
lean_dec_ref(v_vals_1463_);
lean_dec_ref(v_keys_1462_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_x_1470_, v_x_1471_, v_x_1472_, v_x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
if (lean_obj_tag(v_a_1475_) == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_array_to_list(v_a_1476_);
return v___x_1477_;
}
else
{
lean_object* v_head_1478_; 
v_head_1478_ = lean_ctor_get(v_a_1475_, 0);
if (lean_obj_tag(v_head_1478_) == 0)
{
lean_object* v_tail_1479_; 
v_tail_1479_ = lean_ctor_get(v_a_1475_, 1);
lean_inc(v_tail_1479_);
lean_dec_ref_known(v_a_1475_, 2);
v_a_1475_ = v_tail_1479_;
goto _start;
}
else
{
lean_object* v_tail_1481_; lean_object* v_val_1482_; lean_object* v___x_1483_; 
lean_inc_ref(v_head_1478_);
v_tail_1481_ = lean_ctor_get(v_a_1475_, 1);
lean_inc(v_tail_1481_);
lean_dec_ref_known(v_a_1475_, 2);
v_val_1482_ = lean_ctor_get(v_head_1478_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v_head_1478_, 1);
v___x_1483_ = lean_array_push(v_a_1476_, v_val_1482_);
v_a_1475_ = v_tail_1481_;
v_a_1476_ = v___x_1483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg(lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; uint8_t v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = 0;
v___x_1496_ = 1;
v___x_1497_ = l_Lean_Elab_Tactic_Conv_congr(v_a_1494_, v___x_1495_, v___x_1496_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0));
v___x_1500_ = l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(v_a_1498_, v___x_1499_);
v___x_1501_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1500_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
return v___x_1501_;
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1497_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1497_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_a_1510_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1493_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1493_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___boxed(lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr(lean_object* v_x_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1527_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___boxed(lean_object* v_x_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Elab_Tactic_Conv_evalCongr(v_x_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_x_1536_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1(){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1561_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1562_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0));
v___x_1563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1564_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCongr___boxed), 10, 0);
v___x_1565_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1561_, v___x_1562_, v___x_1563_, v___x_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___boxed(lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3(){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1595_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6));
v___x_1596_ = l_Lean_addBuiltinDeclarationRanges(v___x_1594_, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___boxed(lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(lean_object* v_as_1599_, size_t v_i_1600_, size_t v_stop_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_usize_dec_eq(v_i_1600_, v_stop_1601_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_array_uget_borrowed(v_as_1599_, v_i_1600_);
lean_inc(v___x_1609_);
v___x_1610_ = l_Lean_Meta_mkCongrFun(v_b_1602_, v___x_1609_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; size_t v___x_1612_; size_t v___x_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1600_, v___x_1612_);
v_i_1600_ = v___x_1613_;
v_b_1602_ = v_a_1611_;
goto _start;
}
else
{
return v___x_1610_;
}
}
else
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_b_1602_);
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0___boxed(lean_object* v_as_1616_, lean_object* v_i_1617_, lean_object* v_stop_1618_, lean_object* v_b_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
size_t v_i_boxed_1625_; size_t v_stop_boxed_1626_; lean_object* v_res_1627_; 
v_i_boxed_1625_ = lean_unbox_usize(v_i_1617_);
lean_dec(v_i_1617_);
v_stop_boxed_1626_ = lean_unbox_usize(v_stop_1618_);
lean_dec(v_stop_1618_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_as_1616_, v_i_boxed_1625_, v_stop_boxed_1626_, v_b_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec_ref(v_as_1616_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(lean_object* v_mvarId_1629_, lean_object* v_snd_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
if (lean_obj_tag(v_x_1631_) == 5)
{
lean_object* v_fn_1639_; lean_object* v_arg_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_fn_1639_ = lean_ctor_get(v_x_1631_, 0);
lean_inc_ref(v_fn_1639_);
v_arg_1640_ = lean_ctor_get(v_x_1631_, 1);
lean_inc_ref(v_arg_1640_);
lean_dec_ref_known(v_x_1631_, 2);
v___x_1641_ = lean_array_set(v_x_1632_, v_x_1633_, v_arg_1640_);
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_nat_sub(v_x_1633_, v___x_1642_);
lean_dec(v_x_1633_);
v_x_1631_ = v_fn_1639_;
v_x_1632_ = v___x_1641_;
v_x_1633_ = v___x_1643_;
goto _start;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_x_1633_);
v___x_1645_ = lean_box(0);
v___x_1646_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_x_1631_, v___x_1645_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v_fst_1648_; lean_object* v_snd_1649_; lean_object* v_a_1651_; lean_object* v___y_1674_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
v_fst_1648_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_fst_1648_);
v_snd_1649_ = lean_ctor_get(v_a_1647_, 1);
lean_inc(v_snd_1649_);
lean_dec(v_a_1647_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = lean_array_get_size(v_x_1632_);
v___x_1686_ = lean_nat_dec_lt(v___x_1684_, v___x_1685_);
if (v___x_1686_ == 0)
{
lean_inc(v_snd_1649_);
v_a_1651_ = v_snd_1649_;
goto v___jp_1650_;
}
else
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_nat_dec_le(v___x_1685_, v___x_1685_);
if (v___x_1687_ == 0)
{
if (v___x_1686_ == 0)
{
lean_inc(v_snd_1649_);
v_a_1651_ = v_snd_1649_;
goto v___jp_1650_;
}
else
{
size_t v___x_1688_; size_t v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = ((size_t)0ULL);
v___x_1689_ = lean_usize_of_nat(v___x_1685_);
lean_inc(v_snd_1649_);
v___x_1690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1632_, v___x_1688_, v___x_1689_, v_snd_1649_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
v___y_1674_ = v___x_1690_;
goto v___jp_1673_;
}
}
else
{
size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((size_t)0ULL);
v___x_1692_ = lean_usize_of_nat(v___x_1685_);
lean_inc(v_snd_1649_);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1632_, v___x_1691_, v___x_1692_, v_snd_1649_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
v___y_1674_ = v___x_1693_;
goto v___jp_1673_;
}
}
v___jp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1629_, v_a_1651_, v___y_1635_);
lean_dec_ref(v___x_1652_);
v___x_1653_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0));
v___x_1654_ = l_Lean_mkAppN(v_fst_1648_, v_x_1632_);
lean_dec_ref(v_x_1632_);
v___x_1655_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_1653_, v_snd_1630_, v___x_1654_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1663_; 
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v___x_1655_, 0);
lean_dec(v_unused_1664_);
v___x_1657_ = v___x_1655_;
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
else
{
lean_dec(v___x_1655_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lean_Expr_mvarId_x21(v_snd_1649_);
lean_dec(v_snd_1649_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec(v_snd_1649_);
v_a_1665_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1655_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1655_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
v___jp_1673_:
{
if (lean_obj_tag(v___y_1674_) == 0)
{
lean_object* v_a_1675_; 
v_a_1675_ = lean_ctor_get(v___y_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___y_1674_, 1);
v_a_1651_ = v_a_1675_;
goto v___jp_1650_;
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_snd_1649_);
lean_dec(v_fst_1648_);
lean_dec_ref(v_x_1632_);
lean_dec_ref(v_snd_1630_);
lean_dec(v_mvarId_1629_);
v_a_1676_ = lean_ctor_get(v___y_1674_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___y_1674_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___y_1674_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___y_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref(v_x_1632_);
lean_dec_ref(v_snd_1630_);
lean_dec(v_mvarId_1629_);
v_a_1694_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1646_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1646_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___boxed(lean_object* v_mvarId_1702_, lean_object* v_snd_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1702_, v_snd_1703_, v_x_1704_, v_x_1705_, v_x_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
return v_res_1712_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0));
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(lean_object* v_mvarId_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
lean_inc(v_mvarId_1716_);
v___x_1722_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v_fst_1724_; lean_object* v_snd_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1758_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v_fst_1724_ = lean_ctor_get(v_a_1723_, 0);
v_snd_1725_ = lean_ctor_get(v_a_1723_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_a_1723_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1727_ = v_a_1723_;
v_isShared_1728_ = v_isSharedCheck_1758_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snd_1725_);
lean_inc(v_fst_1724_);
lean_dec(v_a_1723_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1758_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; uint8_t v___x_1743_; 
v___x_1729_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1724_, v___y_1718_);
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = l_Lean_Expr_cleanupAnnotations(v_a_1730_);
v___x_1743_ = l_Lean_Expr_isApp(v___x_1731_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1747_; 
lean_dec(v_snd_1725_);
lean_dec(v_mvarId_1716_);
v___x_1744_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1);
v___x_1745_ = l_Lean_indentExpr(v___x_1731_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 7);
lean_ctor_set(v___x_1727_, 1, v___x_1745_);
lean_ctor_set(v___x_1727_, 0, v___x_1744_);
v___x_1747_ = v___x_1727_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1748_; lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
v___x_1748_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1747_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_del_object(v___x_1727_);
v___y_1733_ = v___y_1717_;
v___y_1734_ = v___y_1718_;
v___y_1735_ = v___y_1719_;
v___y_1736_ = v___y_1720_;
goto v___jp_1732_;
}
v___jp_1732_:
{
lean_object* v_dummy_1737_; lean_object* v_nargs_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_dummy_1737_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1738_ = l_Lean_Expr_getAppNumArgs(v___x_1731_);
lean_inc(v_nargs_1738_);
v___x_1739_ = lean_mk_array(v_nargs_1738_, v_dummy_1737_);
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_nat_sub(v_nargs_1738_, v___x_1740_);
lean_dec(v_nargs_1738_);
v___x_1742_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1716_, v_snd_1725_, v___x_1731_, v___x_1739_, v___x_1741_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1742_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_mvarId_1716_);
v_a_1759_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1722_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1722_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed(lean_object* v_mvarId_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(v_mvarId_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN(lean_object* v_mvarId_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v___f_1780_; lean_object* v___x_1781_; 
lean_inc(v_mvarId_1774_);
v___f_1780_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1780_, 0, v_mvarId_1774_);
v___x_1781_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1774_, v___f_1780_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___boxed(lean_object* v_mvarId_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_mvarId_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(lean_object* v_msg_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_panic_fn_borrowed(v___x_1790_, v_msg_1789_);
return v___x_1791_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1793_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_1794_ = lean_unsigned_to_nat(30u);
v___x_1795_ = lean_unsigned_to_nat(150u);
v___x_1796_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__0));
v___x_1797_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_1798_ = l_mkPanicMessageWithDecl(v___x_1797_, v___x_1796_, v___x_1795_, v___x_1794_, v___x_1793_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(lean_object* v_fst_1799_, lean_object* v_snd_1800_, lean_object* v_fst_1801_, lean_object* v_fst_1802_, lean_object* v_00___1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1);
v___x_1810_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_1809_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1821_; 
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1810_, 0);
lean_dec(v_unused_1822_);
v___x_1812_ = v___x_1810_;
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
else
{
lean_dec(v___x_1810_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_fst_1799_);
lean_ctor_set(v___x_1814_, 1, v_snd_1800_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_fst_1801_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_fst_1802_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1817_);
v___x_1819_ = v___x_1812_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_fst_1802_);
lean_dec(v_fst_1801_);
lean_dec(v_snd_1800_);
lean_dec(v_fst_1799_);
v_a_1823_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1810_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1810_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___boxed(lean_object* v_fst_1831_, lean_object* v_snd_1832_, lean_object* v_fst_1833_, lean_object* v_fst_1834_, lean_object* v_00___1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1831_, v_snd_1832_, v_fst_1833_, v_fst_1834_, v_00___1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(lean_object* v_snd_1842_, lean_object* v_snd_1843_, lean_object* v___x_1844_, lean_object* v___x_1845_, lean_object* v_____r_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1852_ = l_Lean_Expr_mvarId_x21(v_snd_1842_);
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v_snd_1843_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1844_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1845_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1___boxed(lean_object* v_snd_1859_, lean_object* v_snd_1860_, lean_object* v___x_1861_, lean_object* v___x_1862_, lean_object* v_____r_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1859_, v_snd_1860_, v___x_1861_, v___x_1862_, v_____r_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec_ref(v_snd_1859_);
return v_res_1869_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__0));
v___x_1872_ = l_Lean_stringToMessageData(v___x_1871_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(lean_object* v_upperBound_1873_, lean_object* v_args_1874_, lean_object* v___x_1875_, lean_object* v_origTag_1876_, lean_object* v_tacticName_1877_, lean_object* v_a_1878_, lean_object* v_b_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_a_1886_; lean_object* v___y_1891_; uint8_t v___x_1910_; 
v___x_1910_ = lean_nat_dec_lt(v_a_1878_, v_upperBound_1873_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_b_1879_);
return v___x_1911_;
}
else
{
lean_object* v_snd_1912_; lean_object* v_snd_1913_; lean_object* v_fst_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_2035_; 
v_snd_1912_ = lean_ctor_get(v_b_1879_, 1);
lean_inc(v_snd_1912_);
v_snd_1913_ = lean_ctor_get(v_snd_1912_, 1);
lean_inc(v_snd_1913_);
v_fst_1914_ = lean_ctor_get(v_b_1879_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_b_1879_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_b_1879_, 1);
lean_dec(v_unused_2036_);
v___x_1916_ = v_b_1879_;
v_isShared_1917_ = v_isSharedCheck_2035_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_fst_1914_);
lean_dec(v_b_1879_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_2035_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_fst_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_2033_; 
v_fst_1918_ = lean_ctor_get(v_snd_1912_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v_snd_1912_);
if (v_isSharedCheck_2033_ == 0)
{
lean_object* v_unused_2034_; 
v_unused_2034_ = lean_ctor_get(v_snd_1912_, 1);
lean_dec(v_unused_2034_);
v___x_1920_ = v_snd_1912_;
v_isShared_1921_ = v_isSharedCheck_2033_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_fst_1918_);
lean_dec(v_snd_1912_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_2033_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_fst_1922_; lean_object* v_snd_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_2032_; 
v_fst_1922_ = lean_ctor_get(v_snd_1913_, 0);
v_snd_1923_ = lean_ctor_get(v_snd_1913_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_snd_1913_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1925_ = v_snd_1913_;
v_isShared_1926_ = v_isSharedCheck_2032_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_snd_1923_);
lean_inc(v_fst_1922_);
lean_dec(v_snd_1913_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_2032_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1927_ = l_Lean_instInhabitedExpr;
v___x_1928_ = lean_array_get_borrowed(v___x_1927_, v_args_1874_, v_a_1878_);
v___x_1929_ = lean_array_fget_borrowed(v___x_1875_, v_a_1878_);
v___x_1930_ = lean_unbox(v___x_1929_);
switch(v___x_1930_)
{
case 1:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_del_object(v___x_1925_);
lean_del_object(v___x_1920_);
lean_del_object(v___x_1916_);
v___x_1931_ = lean_box(0);
v___x_1932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1922_, v_snd_1923_, v_fst_1918_, v_fst_1914_, v___x_1931_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
v___y_1891_ = v___x_1932_;
goto v___jp_1890_;
}
case 2:
{
lean_object* v___x_1933_; 
lean_del_object(v___x_1925_);
lean_del_object(v___x_1920_);
lean_del_object(v___x_1916_);
lean_inc(v_origTag_1876_);
lean_inc(v___x_1928_);
v___x_1933_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_1928_, v_origTag_1876_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v_fst_1935_; lean_object* v_snd_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1962_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v_fst_1935_ = lean_ctor_get(v_a_1934_, 0);
v_snd_1936_ = lean_ctor_get(v_a_1934_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1934_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1938_ = v_a_1934_;
v_isShared_1939_ = v_isSharedCheck_1962_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_snd_1936_);
lean_inc(v_fst_1935_);
lean_dec(v_a_1934_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1962_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_inc(v_fst_1935_);
v___x_1940_ = l_Lean_Expr_app___override(v_fst_1914_, v_fst_1935_);
lean_inc(v_snd_1936_);
lean_inc(v___x_1928_);
v___x_1941_ = l_Lean_mkApp3(v_fst_1918_, v___x_1928_, v_fst_1935_, v_snd_1936_);
if (lean_obj_tag(v_fst_1922_) == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_del_object(v___x_1938_);
v___x_1942_ = lean_box(0);
v___x_1943_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1936_, v_snd_1923_, v___x_1941_, v___x_1940_, v___x_1942_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v_snd_1936_);
v___y_1891_ = v___x_1943_;
goto v___jp_1890_;
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_dec_ref_known(v_fst_1922_, 1);
v___x_1944_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
lean_inc_ref(v_tacticName_1877_);
v___x_1945_ = l_Lean_stringToMessageData(v_tacticName_1877_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 7);
lean_ctor_set(v___x_1938_, 1, v___x_1945_);
lean_ctor_set(v___x_1938_, 0, v___x_1944_);
v___x_1947_ = v___x_1938_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1949_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1936_, v_snd_1923_, v___x_1941_, v___x_1940_, v_a_1951_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v_snd_1936_);
v___y_1891_ = v___x_1952_;
goto v___jp_1890_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v___x_1941_);
lean_dec_ref(v___x_1940_);
lean_dec(v_snd_1936_);
lean_dec(v_snd_1923_);
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v_a_1953_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1950_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1950_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_snd_1923_);
lean_dec(v_fst_1922_);
lean_dec(v_fst_1918_);
lean_dec(v_fst_1914_);
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v_a_1963_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1933_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1933_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
case 4:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_del_object(v___x_1925_);
lean_del_object(v___x_1920_);
lean_del_object(v___x_1916_);
v___x_1971_ = lean_box(0);
v___x_1972_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1922_, v_snd_1923_, v_fst_1918_, v_fst_1914_, v___x_1971_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
v___y_1891_ = v___x_1972_;
goto v___jp_1890_;
}
case 5:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_inc(v___x_1928_);
v___x_1973_ = l_Lean_Expr_app___override(v_fst_1918_, v___x_1928_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
lean_inc_ref(v___x_1973_);
v___x_1974_ = lean_infer_type(v___x_1973_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
v___x_1976_ = lean_whnf(v_a_1975_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = l_Lean_Expr_bindingDomain_x21(v_a_1977_);
lean_dec(v_a_1977_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
v___x_1980_ = 0;
v___x_1981_ = lean_box(0);
v___x_1982_ = l_Lean_Meta_mkFreshExprMVar(v___x_1979_, v___x_1980_, v___x_1981_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc_n(v_a_1983_, 3);
lean_dec_ref_known(v___x_1982_, 1);
v___x_1984_ = l_Lean_Expr_app___override(v_fst_1914_, v_a_1983_);
v___x_1985_ = l_Lean_Expr_app___override(v___x_1973_, v_a_1983_);
v___x_1986_ = l_Lean_Expr_mvarId_x21(v_a_1983_);
lean_dec(v_a_1983_);
v___x_1987_ = lean_array_push(v_snd_1923_, v___x_1986_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 1, v___x_1987_);
v___x_1989_ = v___x_1925_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_fst_1922_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___x_1989_);
lean_ctor_set(v___x_1920_, 0, v___x_1985_);
v___x_1991_ = v___x_1920_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v___x_1991_);
lean_ctor_set(v___x_1916_, 0, v___x_1984_);
v___x_1993_ = v___x_1916_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
v_a_1886_ = v___x_1993_;
goto v___jp_1885_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec_ref(v___x_1973_);
lean_del_object(v___x_1925_);
lean_dec(v_snd_1923_);
lean_dec(v_fst_1922_);
lean_del_object(v___x_1920_);
lean_del_object(v___x_1916_);
lean_dec(v_fst_1914_);
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v_a_1997_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1982_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1982_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v___x_1973_);
lean_del_object(v___x_1925_);
lean_dec(v_snd_1923_);
lean_dec(v_fst_1922_);
lean_del_object(v___x_1920_);
lean_del_object(v___x_1916_);
lean_dec(v_fst_1914_);
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v_a_2005_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1976_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1976_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v___x_1973_);
lean_del_object(v___x_1925_);
lean_dec(v_snd_1923_);
lean_dec(v_fst_1922_);
lean_del_object(v___x_1920_);
lean_del_object(v___x_1916_);
lean_dec(v_fst_1914_);
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v_a_2013_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1974_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1974_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
default: 
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_inc_n(v___x_1928_, 2);
v___x_2021_ = l_Lean_Expr_app___override(v_fst_1914_, v___x_1928_);
v___x_2022_ = l_Lean_Expr_app___override(v_fst_1918_, v___x_1928_);
if (v_isShared_1926_ == 0)
{
v___x_2024_ = v___x_1925_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_fst_1922_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_snd_1923_);
v___x_2024_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___x_2024_);
lean_ctor_set(v___x_1920_, 0, v___x_2022_);
v___x_2026_ = v___x_1920_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v___x_2026_);
lean_ctor_set(v___x_1916_, 0, v___x_2021_);
v___x_2028_ = v___x_1916_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
v_a_1886_ = v___x_2028_;
goto v___jp_1885_;
}
}
}
}
}
}
}
}
}
v___jp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_nat_add(v_a_1878_, v___x_1887_);
lean_dec(v_a_1878_);
v_a_1878_ = v___x_1888_;
v_b_1879_ = v_a_1886_;
goto _start;
}
v___jp_1890_:
{
if (lean_obj_tag(v___y_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1901_; 
v_a_1892_ = lean_ctor_get(v___y_1891_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___y_1891_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1894_ = v___y_1891_;
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___y_1891_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1901_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
if (lean_obj_tag(v_a_1892_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; 
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v_a_1896_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v_a_1892_, 1);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v_a_1896_);
v___x_1898_ = v___x_1894_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
else
{
lean_object* v_a_1900_; 
lean_del_object(v___x_1894_);
v_a_1900_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v_a_1892_, 1);
v_a_1886_ = v_a_1900_;
goto v___jp_1885_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1878_);
lean_dec_ref(v_tacticName_1877_);
lean_dec(v_origTag_1876_);
v_a_1902_ = lean_ctor_get(v___y_1891_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___y_1891_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___y_1891_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___y_1891_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___boxed(lean_object* v_upperBound_2037_, lean_object* v_args_2038_, lean_object* v___x_2039_, lean_object* v_origTag_2040_, lean_object* v_tacticName_2041_, lean_object* v_a_2042_, lean_object* v_b_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2037_, v_args_2038_, v___x_2039_, v_origTag_2040_, v_tacticName_2041_, v_a_2042_, v_b_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec_ref(v___x_2039_);
lean_dec_ref(v_args_2038_);
lean_dec(v_upperBound_2037_);
return v_res_2049_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2));
v___x_2054_ = lean_unsigned_to_nat(14u);
v___x_2055_ = lean_unsigned_to_nat(22u);
v___x_2056_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1));
v___x_2057_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0));
v___x_2058_ = l_mkPanicMessageWithDecl(v___x_2057_, v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_);
return v___x_2058_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5));
v___x_2064_ = l_Lean_stringToMessageData(v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(lean_object* v_tacticName_2065_, lean_object* v_origTag_2066_, lean_object* v_f_2067_, lean_object* v_args_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v_lower_2089_; lean_object* v_upper_2090_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_array_get_size(v_args_2068_);
lean_inc_ref(v_f_2067_);
v___x_2107_ = l_Lean_Meta_getFunInfoNArgs(v_f_2067_, v___x_2106_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_a_2108_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = 0;
lean_inc_ref(v_f_2067_);
v___x_2112_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_2067_, v_a_2108_, v_a_2110_, v___x_2111_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
if (lean_obj_tag(v_a_2113_) == 1)
{
lean_object* v_val_2114_; lean_object* v_proof_2115_; lean_object* v_argKinds_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v_val_2114_ = lean_ctor_get(v_a_2113_, 0);
lean_inc(v_val_2114_);
lean_dec_ref_known(v_a_2113_, 1);
v_proof_2115_ = lean_ctor_get(v_val_2114_, 1);
lean_inc_ref(v_proof_2115_);
v_argKinds_2116_ = lean_ctor_get(v_val_2114_, 2);
lean_inc_ref(v_argKinds_2116_);
lean_dec(v_val_2114_);
v___x_2143_ = 0;
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_box(v___x_2143_);
v___x_2146_ = lean_array_get(v___x_2145_, v_argKinds_2116_, v___x_2144_);
lean_dec(v___x_2145_);
v___x_2147_ = lean_unbox(v___x_2146_);
lean_dec(v___x_2146_);
if (v___x_2147_ == 2)
{
v___y_2118_ = v_a_2069_;
v___y_2119_ = v_a_2070_;
v___y_2120_ = v_a_2071_;
v___y_2121_ = v_a_2072_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_argKinds_2116_);
lean_dec_ref(v_proof_2115_);
lean_dec_ref(v_args_2068_);
lean_dec_ref(v_f_2067_);
lean_dec(v_origTag_2066_);
v___x_2148_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2149_ = l_Lean_stringToMessageData(v_tacticName_2065_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2152_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
v___jp_2117_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2122_ = lean_array_get_size(v_argKinds_2116_);
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4));
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_proof_2115_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_f_2067_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v___x_2122_, v_args_2068_, v_argKinds_2116_, v_origTag_2066_, v_tacticName_2065_, v___x_2123_, v___x_2126_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec_ref(v_argKinds_2116_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v_snd_2129_; lean_object* v_snd_2130_; lean_object* v_fst_2131_; lean_object* v_fst_2132_; lean_object* v_snd_2133_; uint8_t v___x_2134_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref_known(v___x_2127_, 1);
v_snd_2129_ = lean_ctor_get(v_a_2128_, 1);
lean_inc(v_snd_2129_);
lean_dec(v_a_2128_);
v_snd_2130_ = lean_ctor_get(v_snd_2129_, 1);
lean_inc(v_snd_2130_);
v_fst_2131_ = lean_ctor_get(v_snd_2129_, 0);
lean_inc(v_fst_2131_);
lean_dec(v_snd_2129_);
v_fst_2132_ = lean_ctor_get(v_snd_2130_, 0);
lean_inc(v_fst_2132_);
v_snd_2133_ = lean_ctor_get(v_snd_2130_, 1);
lean_inc(v_snd_2133_);
lean_dec(v_snd_2130_);
v___x_2134_ = lean_nat_dec_le(v___x_2122_, v___x_2123_);
if (v___x_2134_ == 0)
{
v___y_2082_ = v_snd_2133_;
v___y_2083_ = v_fst_2131_;
v___y_2084_ = v___y_2118_;
v___y_2085_ = v_fst_2132_;
v___y_2086_ = v___y_2120_;
v___y_2087_ = v___y_2121_;
v___y_2088_ = v___y_2119_;
v_lower_2089_ = v___x_2122_;
v_upper_2090_ = v___x_2106_;
goto v___jp_2081_;
}
else
{
v___y_2082_ = v_snd_2133_;
v___y_2083_ = v_fst_2131_;
v___y_2084_ = v___y_2118_;
v___y_2085_ = v_fst_2132_;
v___y_2086_ = v___y_2120_;
v___y_2087_ = v___y_2121_;
v___y_2088_ = v___y_2119_;
v_lower_2089_ = v___x_2123_;
v_upper_2090_ = v___x_2106_;
goto v___jp_2081_;
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_args_2068_);
v_a_2135_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2127_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2127_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_args_2068_);
lean_dec_ref(v_f_2067_);
lean_dec(v_origTag_2066_);
v___x_2162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2163_ = l_Lean_stringToMessageData(v_tacticName_2065_);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2166_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
return v___x_2167_;
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v_args_2068_);
lean_dec_ref(v_f_2067_);
lean_dec(v_origTag_2066_);
lean_dec_ref(v_tacticName_2065_);
v_a_2168_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2112_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2112_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_a_2108_);
lean_dec_ref(v_args_2068_);
lean_dec_ref(v_f_2067_);
lean_dec(v_origTag_2066_);
lean_dec_ref(v_tacticName_2065_);
v_a_2176_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2109_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2109_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_args_2068_);
lean_dec_ref(v_f_2067_);
lean_dec(v_origTag_2066_);
lean_dec_ref(v_tacticName_2065_);
v_a_2184_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2107_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2107_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
v___jp_2074_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___y_2077_);
lean_ctor_set(v___x_2078_, 1, v___y_2076_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___y_2075_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
v___jp_2081_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = l_Array_toSubarray___redArg(v_args_2068_, v_lower_2089_, v_upper_2090_);
v___x_2092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_2091_, v___y_2083_, v___y_2084_, v___y_2088_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2092_) == 0)
{
if (lean_obj_tag(v___y_2085_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3);
v___x_2095_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(v___x_2094_);
v___y_2075_ = v_a_2093_;
v___y_2076_ = v___y_2082_;
v___y_2077_ = v___x_2095_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2096_; lean_object* v_val_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2092_, 1);
v_val_2097_ = lean_ctor_get(v___y_2085_, 0);
lean_inc(v_val_2097_);
lean_dec_ref_known(v___y_2085_, 1);
v___y_2075_ = v_a_2096_;
v___y_2076_ = v___y_2082_;
v___y_2077_ = v_val_2097_;
goto v___jp_2074_;
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v___y_2085_);
lean_dec(v___y_2082_);
v_a_2098_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2092_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2092_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___boxed(lean_object* v_tacticName_2192_, lean_object* v_origTag_2193_, lean_object* v_f_2194_, lean_object* v_args_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_2192_, v_origTag_2193_, v_f_2194_, v_args_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(lean_object* v_upperBound_2202_, lean_object* v_args_2203_, lean_object* v___x_2204_, lean_object* v_origTag_2205_, lean_object* v_tacticName_2206_, lean_object* v_inst_2207_, lean_object* v_R_2208_, lean_object* v_a_2209_, lean_object* v_b_2210_, lean_object* v_c_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2202_, v_args_2203_, v___x_2204_, v_origTag_2205_, v_tacticName_2206_, v_a_2209_, v_b_2210_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___boxed(lean_object* v_upperBound_2218_, lean_object* v_args_2219_, lean_object* v___x_2220_, lean_object* v_origTag_2221_, lean_object* v_tacticName_2222_, lean_object* v_inst_2223_, lean_object* v_R_2224_, lean_object* v_a_2225_, lean_object* v_b_2226_, lean_object* v_c_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(v_upperBound_2218_, v_args_2219_, v___x_2220_, v_origTag_2221_, v_tacticName_2222_, v_inst_2223_, v_R_2224_, v_a_2225_, v_b_2226_, v_c_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v___x_2220_);
lean_dec_ref(v_args_2219_);
lean_dec(v_upperBound_2218_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(lean_object* v_msg_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___f_2240_; lean_object* v___x_4889__overap_2241_; lean_object* v___x_2242_; 
v___f_2240_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_4889__overap_2241_ = lean_panic_fn_borrowed(v___f_2240_, v_msg_2234_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc(v___y_2236_);
lean_inc_ref(v___y_2235_);
v___x_2242_ = lean_apply_5(v___x_4889__overap_2241_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, lean_box(0));
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1___boxed(lean_object* v_msg_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v_msg_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(lean_object* v_binderType_2253_, lean_object* v_mvarId_2254_, lean_object* v_body_2255_, uint8_t v_domain_2256_, uint8_t v___x_2257_, lean_object* v_binderName_2258_, lean_object* v_tacticName_2259_, lean_object* v_rhs_2260_, lean_object* v_arg_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
lean_inc_ref(v_binderType_2253_);
v___x_2267_ = l_Lean_Meta_getLevel(v_binderType_2253_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2269_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
lean_inc(v_mvarId_2254_);
v___x_2269_ = l_Lean_MVarId_getTag(v_mvarId_2254_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = lean_expr_instantiate1(v_body_2255_, v_arg_2261_);
lean_inc_ref(v___x_2271_);
v___x_2272_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_2271_, v_a_2270_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2349_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
v_fst_2274_ = lean_ctor_get(v_a_2273_, 0);
v_snd_2275_ = lean_ctor_get(v_a_2273_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_a_2273_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2277_ = v_a_2273_;
v_isShared_2278_ = v_isSharedCheck_2349_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_snd_2275_);
lean_inc(v_fst_2274_);
lean_dec(v_a_2273_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2349_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Meta_getLevel(v___x_2271_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_mk_empty_array_with_capacity(v___x_2281_);
v___x_2283_ = lean_array_push(v___x_2282_, v_arg_2261_);
v___x_2284_ = 1;
v___x_2285_ = l_Lean_Meta_mkLambdaFVars(v___x_2283_, v_fst_2274_, v_domain_2256_, v___x_2257_, v_domain_2256_, v___x_2257_, v___x_2284_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
lean_inc(v_snd_2275_);
v___x_2287_ = l_Lean_Meta_mkLambdaFVars(v___x_2283_, v_snd_2275_, v_domain_2256_, v___x_2257_, v_domain_2256_, v___x_2257_, v___x_2284_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec_ref(v___x_2283_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1));
v___x_2290_ = lean_box(0);
if (v_isShared_2278_ == 0)
{
lean_ctor_set_tag(v___x_2277_, 1);
lean_ctor_set(v___x_2277_, 1, v___x_2290_);
lean_ctor_set(v___x_2277_, 0, v_a_2280_);
v___x_2292_ = v___x_2277_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2280_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2293_, 0, v_a_2268_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_Expr_const___override(v___x_2289_, v___x_2293_);
v___x_2295_ = 0;
lean_inc_ref(v_binderType_2253_);
v___x_2296_ = l_Lean_Expr_lam___override(v_binderName_2258_, v_binderType_2253_, v_body_2255_, v___x_2295_);
v___x_2297_ = lean_unsigned_to_nat(4u);
v___x_2298_ = lean_mk_empty_array_with_capacity(v___x_2297_);
v___x_2299_ = lean_array_push(v___x_2298_, v_binderType_2253_);
v___x_2300_ = lean_array_push(v___x_2299_, v___x_2296_);
v___x_2301_ = lean_array_push(v___x_2300_, v_a_2286_);
v___x_2302_ = lean_array_push(v___x_2301_, v_a_2288_);
v___x_2303_ = l_Lean_mkAppN(v___x_2294_, v___x_2302_);
lean_dec_ref(v___x_2302_);
lean_inc_ref(v___x_2303_);
v___x_2304_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2259_, v_rhs_2260_, v___x_2303_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref_known(v___x_2304_, 1);
v___x_2305_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2254_, v___x_2303_, v___y_2263_);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v___x_2305_, 0);
lean_dec(v_unused_2315_);
v___x_2307_ = v___x_2305_;
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
else
{
lean_dec(v___x_2305_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2309_ = l_Lean_Expr_mvarId_x21(v_snd_2275_);
lean_dec(v_snd_2275_);
v___x_2310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2290_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2310_);
v___x_2312_ = v___x_2307_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v___x_2303_);
lean_dec(v_snd_2275_);
lean_dec(v_mvarId_2254_);
v_a_2316_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2304_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2304_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_a_2286_);
lean_dec(v_a_2280_);
lean_del_object(v___x_2277_);
lean_dec(v_snd_2275_);
lean_dec(v_a_2268_);
lean_dec_ref(v_rhs_2260_);
lean_dec_ref(v_tacticName_2259_);
lean_dec(v_binderName_2258_);
lean_dec_ref(v_body_2255_);
lean_dec(v_mvarId_2254_);
lean_dec_ref(v_binderType_2253_);
v_a_2325_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2287_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2287_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v___x_2283_);
lean_dec(v_a_2280_);
lean_del_object(v___x_2277_);
lean_dec(v_snd_2275_);
lean_dec(v_a_2268_);
lean_dec_ref(v_rhs_2260_);
lean_dec_ref(v_tacticName_2259_);
lean_dec(v_binderName_2258_);
lean_dec_ref(v_body_2255_);
lean_dec(v_mvarId_2254_);
lean_dec_ref(v_binderType_2253_);
v_a_2333_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2285_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2285_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_del_object(v___x_2277_);
lean_dec(v_snd_2275_);
lean_dec(v_fst_2274_);
lean_dec(v_a_2268_);
lean_dec_ref(v_arg_2261_);
lean_dec_ref(v_rhs_2260_);
lean_dec_ref(v_tacticName_2259_);
lean_dec(v_binderName_2258_);
lean_dec_ref(v_body_2255_);
lean_dec(v_mvarId_2254_);
lean_dec_ref(v_binderType_2253_);
v_a_2341_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2279_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2279_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___x_2271_);
lean_dec(v_a_2268_);
lean_dec_ref(v_arg_2261_);
lean_dec_ref(v_rhs_2260_);
lean_dec_ref(v_tacticName_2259_);
lean_dec(v_binderName_2258_);
lean_dec_ref(v_body_2255_);
lean_dec(v_mvarId_2254_);
lean_dec_ref(v_binderType_2253_);
v_a_2350_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2272_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2272_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_2268_);
lean_dec_ref(v_arg_2261_);
lean_dec_ref(v_rhs_2260_);
lean_dec_ref(v_tacticName_2259_);
lean_dec(v_binderName_2258_);
lean_dec_ref(v_body_2255_);
lean_dec(v_mvarId_2254_);
lean_dec_ref(v_binderType_2253_);
v_a_2358_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2269_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2269_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec_ref(v_arg_2261_);
lean_dec_ref(v_rhs_2260_);
lean_dec_ref(v_tacticName_2259_);
lean_dec(v_binderName_2258_);
lean_dec_ref(v_body_2255_);
lean_dec(v_mvarId_2254_);
lean_dec_ref(v_binderType_2253_);
v_a_2366_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2267_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2267_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed(lean_object* v_binderType_2374_, lean_object* v_mvarId_2375_, lean_object* v_body_2376_, lean_object* v_domain_2377_, lean_object* v___x_2378_, lean_object* v_binderName_2379_, lean_object* v_tacticName_2380_, lean_object* v_rhs_2381_, lean_object* v_arg_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
uint8_t v_domain_boxed_2388_; uint8_t v___x_5312__boxed_2389_; lean_object* v_res_2390_; 
v_domain_boxed_2388_ = lean_unbox(v_domain_2377_);
v___x_5312__boxed_2389_ = lean_unbox(v___x_2378_);
v_res_2390_ = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(v_binderType_2374_, v_mvarId_2375_, v_body_2376_, v_domain_boxed_2388_, v___x_5312__boxed_2389_, v_binderName_2379_, v_tacticName_2380_, v_rhs_2381_, v_arg_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2391_, lean_object* v_b_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
lean_inc(v___y_2396_);
lean_inc_ref(v___y_2395_);
lean_inc(v___y_2394_);
lean_inc_ref(v___y_2393_);
v___x_2398_ = lean_apply_6(v_k_2391_, v_b_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, lean_box(0));
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2399_, lean_object* v_b_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(v_k_2399_, v_b_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(lean_object* v_name_2407_, uint8_t v_bi_2408_, lean_object* v_type_2409_, lean_object* v_k_2410_, uint8_t v_kind_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___f_2417_; lean_object* v___x_2418_; 
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2417_, 0, v_k_2410_);
v___x_2418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2407_, v_bi_2408_, v_type_2409_, v___f_2417_, v_kind_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
v_a_2427_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2418_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2418_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_2435_, lean_object* v_bi_2436_, lean_object* v_type_2437_, lean_object* v_k_2438_, lean_object* v_kind_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v_bi_boxed_2445_; uint8_t v_kind_boxed_2446_; lean_object* v_res_2447_; 
v_bi_boxed_2445_ = lean_unbox(v_bi_2436_);
v_kind_boxed_2446_ = lean_unbox(v_kind_2439_);
v_res_2447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2435_, v_bi_boxed_2445_, v_type_2437_, v_k_2438_, v_kind_boxed_2446_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(lean_object* v_name_2448_, lean_object* v_type_2449_, lean_object* v_k_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
uint8_t v___x_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = 0;
v___x_2457_ = 0;
v___x_2458_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2448_, v___x_2456_, v_type_2449_, v_k_2450_, v___x_2457_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg___boxed(lean_object* v_name_2459_, lean_object* v_type_2460_, lean_object* v_k_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2459_, v_type_2460_, v_k_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0));
v___x_2470_ = l_Lean_stringToMessageData(v___x_2469_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2475_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_2476_ = lean_unsigned_to_nat(33u);
v___x_2477_ = lean_unsigned_to_nat(158u);
v___x_2478_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4));
v___x_2479_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_2480_ = l_mkPanicMessageWithDecl(v___x_2479_, v___x_2478_, v___x_2477_, v___x_2476_, v___x_2475_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall(lean_object* v_tacticName_2481_, uint8_t v_domain_2482_, lean_object* v_mvarId_2483_, lean_object* v_lhs_2484_, lean_object* v_rhs_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
if (lean_obj_tag(v_lhs_2484_) == 7)
{
lean_object* v_binderName_2491_; lean_object* v_binderType_2492_; lean_object* v_body_2493_; uint8_t v_binderInfo_2494_; lean_object* v___y_2496_; 
v_binderName_2491_ = lean_ctor_get(v_lhs_2484_, 0);
lean_inc(v_binderName_2491_);
v_binderType_2492_ = lean_ctor_get(v_lhs_2484_, 1);
lean_inc_ref(v_binderType_2492_);
v_body_2493_ = lean_ctor_get(v_lhs_2484_, 2);
lean_inc_ref(v_body_2493_);
v_binderInfo_2494_ = lean_ctor_get_uint8(v_lhs_2484_, sizeof(void*)*3 + 8);
if (v_domain_2482_ == 0)
{
lean_object* v___x_2579_; 
lean_dec_ref_known(v_lhs_2484_, 3);
lean_inc(v_binderName_2491_);
v___x_2579_ = l_Lean_Core_mkFreshUserName(v_binderName_2491_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = 1;
v___x_2582_ = lean_box(v_domain_2482_);
v___x_2583_ = lean_box(v___x_2581_);
lean_inc_ref(v_binderType_2492_);
v___f_2584_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed), 14, 8);
lean_closure_set(v___f_2584_, 0, v_binderType_2492_);
lean_closure_set(v___f_2584_, 1, v_mvarId_2483_);
lean_closure_set(v___f_2584_, 2, v_body_2493_);
lean_closure_set(v___f_2584_, 3, v___x_2582_);
lean_closure_set(v___f_2584_, 4, v___x_2583_);
lean_closure_set(v___f_2584_, 5, v_binderName_2491_);
lean_closure_set(v___f_2584_, 6, v_tacticName_2481_);
lean_closure_set(v___f_2584_, 7, v_rhs_2485_);
v___x_2585_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_a_2580_, v_binderType_2492_, v___f_2584_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
return v___x_2585_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v_body_2493_);
lean_dec_ref(v_binderType_2492_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2586_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2579_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2579_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
else
{
uint8_t v___x_2594_; 
v___x_2594_ = l_Lean_Expr_hasLooseBVars(v_body_2493_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_dec_ref_known(v_lhs_2484_, 3);
lean_inc(v_mvarId_2483_);
v___x_2595_ = l_Lean_MVarId_getTag(v_mvarId_2483_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2492_, v_a_2596_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_fst_2599_; lean_object* v_snd_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2653_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v_fst_2599_ = lean_ctor_get(v_a_2598_, 0);
v_snd_2600_ = lean_ctor_get(v_a_2598_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_a_2598_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2602_ = v_a_2598_;
v_isShared_2603_ = v_isSharedCheck_2653_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_snd_2600_);
lean_inc(v_fst_2599_);
lean_dec(v_a_2598_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2653_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; 
lean_inc_ref(v_body_2493_);
v___x_2604_ = l_Lean_Meta_mkEqRefl(v_body_2493_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1));
v___x_2607_ = lean_unsigned_to_nat(2u);
v___x_2608_ = lean_mk_empty_array_with_capacity(v___x_2607_);
lean_inc(v_snd_2600_);
v___x_2609_ = lean_array_push(v___x_2608_, v_snd_2600_);
v___x_2610_ = lean_array_push(v___x_2609_, v_a_2605_);
v___x_2611_ = l_Lean_Meta_mkAppM(v___x_2606_, v___x_2610_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v___x_2613_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2483_, v_a_2612_, v_a_2487_);
lean_dec_ref(v___x_2613_);
v___x_2614_ = l_Lean_Expr_forallE___override(v_binderName_2491_, v_fst_2599_, v_body_2493_, v_binderInfo_2494_);
v___x_2615_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_2481_, v_rhs_2485_, v___x_2614_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2627_; 
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v___x_2615_, 0);
lean_dec(v_unused_2628_);
v___x_2617_ = v___x_2615_;
v_isShared_2618_ = v_isSharedCheck_2627_;
goto v_resetjp_2616_;
}
else
{
lean_dec(v___x_2615_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2627_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2619_ = l_Lean_Expr_mvarId_x21(v_snd_2600_);
lean_dec(v_snd_2600_);
v___x_2620_ = lean_box(0);
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 1);
lean_ctor_set(v___x_2602_, 1, v___x_2620_);
lean_ctor_set(v___x_2602_, 0, v___x_2619_);
v___x_2622_ = v___x_2602_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2622_);
v___x_2624_ = v___x_2617_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_del_object(v___x_2602_);
lean_dec(v_snd_2600_);
v_a_2629_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2615_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2615_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_del_object(v___x_2602_);
lean_dec(v_snd_2600_);
lean_dec(v_fst_2599_);
lean_dec_ref(v_body_2493_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2637_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2611_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2611_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_del_object(v___x_2602_);
lean_dec(v_snd_2600_);
lean_dec(v_fst_2599_);
lean_dec_ref(v_body_2493_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2645_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2604_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2604_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_body_2493_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2654_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2597_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2597_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v_body_2493_);
lean_dec_ref(v_binderType_2492_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2662_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2595_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2595_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v___x_2670_; 
lean_inc_ref(v_body_2493_);
v___x_2670_ = l_Lean_Meta_isProp(v_body_2493_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; uint8_t v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
v___x_2672_ = lean_unbox(v_a_2671_);
lean_dec(v_a_2671_);
if (v___x_2672_ == 0)
{
lean_dec_ref_known(v_lhs_2484_, 3);
v___y_2496_ = v___x_2670_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2673_; 
lean_dec_ref_known(v___x_2670_, 1);
v___x_2673_ = l_Lean_Meta_isProp(v_lhs_2484_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
v___y_2496_ = v___x_2673_;
goto v___jp_2495_;
}
}
else
{
lean_dec_ref_known(v_lhs_2484_, 3);
v___y_2496_ = v___x_2670_;
goto v___jp_2495_;
}
}
}
v___jp_2495_:
{
if (lean_obj_tag(v___y_2496_) == 0)
{
lean_object* v_a_2497_; uint8_t v___x_2498_; 
v_a_2497_ = lean_ctor_get(v___y_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___y_2496_, 1);
v___x_2498_ = lean_unbox(v_a_2497_);
lean_dec(v_a_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v_body_2493_);
lean_dec_ref(v_binderType_2492_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
v___x_2499_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2500_ = l_Lean_stringToMessageData(v_tacticName_2481_);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2503_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
return v___x_2504_;
}
else
{
lean_object* v___x_2505_; 
lean_inc(v_mvarId_2483_);
v___x_2505_ = l_Lean_MVarId_getTag(v_mvarId_2483_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
lean_inc_ref(v_binderType_2492_);
v___x_2507_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2492_, v_a_2506_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v_snd_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2553_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v_snd_2509_ = lean_ctor_get(v_a_2508_, 1);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v_a_2508_, 0);
lean_dec(v_unused_2554_);
v___x_2511_ = v_a_2508_;
v_isShared_2512_ = v_isSharedCheck_2553_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_snd_2509_);
lean_dec(v_a_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2553_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2513_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3));
v___x_2514_ = 0;
v___x_2515_ = l_Lean_Expr_lam___override(v_binderName_2491_, v_binderType_2492_, v_body_2493_, v___x_2514_);
v___x_2516_ = lean_unsigned_to_nat(2u);
v___x_2517_ = lean_mk_empty_array_with_capacity(v___x_2516_);
lean_inc(v_snd_2509_);
v___x_2518_ = lean_array_push(v___x_2517_, v_snd_2509_);
v___x_2519_ = lean_array_push(v___x_2518_, v___x_2515_);
v___x_2520_ = l_Lean_Meta_mkAppM(v___x_2513_, v___x_2519_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc_n(v_a_2521_, 2);
lean_dec_ref_known(v___x_2520_, 1);
v___x_2522_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2481_, v_rhs_2485_, v_a_2521_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref_known(v___x_2522_, 1);
v___x_2523_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2483_, v_a_2521_, v_a_2487_);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___x_2523_, 0);
lean_dec(v_unused_2536_);
v___x_2525_ = v___x_2523_;
v_isShared_2526_ = v_isSharedCheck_2535_;
goto v_resetjp_2524_;
}
else
{
lean_dec(v___x_2523_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2535_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2527_ = l_Lean_Expr_mvarId_x21(v_snd_2509_);
lean_dec(v_snd_2509_);
v___x_2528_ = lean_box(0);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
lean_ctor_set(v___x_2511_, 1, v___x_2528_);
lean_ctor_set(v___x_2511_, 0, v___x_2527_);
v___x_2530_ = v___x_2511_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2532_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2530_);
v___x_2532_ = v___x_2525_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_a_2521_);
lean_del_object(v___x_2511_);
lean_dec(v_snd_2509_);
lean_dec(v_mvarId_2483_);
v_a_2537_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2522_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2522_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_del_object(v___x_2511_);
lean_dec(v_snd_2509_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2545_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2520_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2520_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v_body_2493_);
lean_dec_ref(v_binderType_2492_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2555_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2507_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2507_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_body_2493_);
lean_dec_ref(v_binderType_2492_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2563_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2505_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2505_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec_ref(v_body_2493_);
lean_dec_ref(v_binderType_2492_);
lean_dec(v_binderName_2491_);
lean_dec_ref(v_rhs_2485_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v_a_2571_ = lean_ctor_get(v___y_2496_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___y_2496_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___y_2496_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___y_2496_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref(v_rhs_2485_);
lean_dec_ref(v_lhs_2484_);
lean_dec(v_mvarId_2483_);
lean_dec_ref(v_tacticName_2481_);
v___x_2674_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5);
v___x_2675_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v___x_2674_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___boxed(lean_object* v_tacticName_2676_, lean_object* v_domain_2677_, lean_object* v_mvarId_2678_, lean_object* v_lhs_2679_, lean_object* v_rhs_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
uint8_t v_domain_boxed_2686_; lean_object* v_res_2687_; 
v_domain_boxed_2686_ = lean_unbox(v_domain_2677_);
v_res_2687_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_2676_, v_domain_boxed_2686_, v_mvarId_2678_, v_lhs_2679_, v_rhs_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_object* v_00_u03b1_2688_, lean_object* v_name_2689_, uint8_t v_bi_2690_, lean_object* v_type_2691_, lean_object* v_k_2692_, uint8_t v_kind_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2689_, v_bi_2690_, v_type_2691_, v_k_2692_, v_kind_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2700_, lean_object* v_name_2701_, lean_object* v_bi_2702_, lean_object* v_type_2703_, lean_object* v_k_2704_, lean_object* v_kind_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
uint8_t v_bi_boxed_2711_; uint8_t v_kind_boxed_2712_; lean_object* v_res_2713_; 
v_bi_boxed_2711_ = lean_unbox(v_bi_2702_);
v_kind_boxed_2712_ = lean_unbox(v_kind_2705_);
v_res_2713_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(v_00_u03b1_2700_, v_name_2701_, v_bi_boxed_2711_, v_type_2703_, v_k_2704_, v_kind_boxed_2712_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_object* v_00_u03b1_2714_, lean_object* v_name_2715_, lean_object* v_type_2716_, lean_object* v_k_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2715_, v_type_2716_, v_k_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___boxed(lean_object* v_00_u03b1_2724_, lean_object* v_name_2725_, lean_object* v_type_2726_, lean_object* v_k_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(v_00_u03b1_2724_, v_name_2725_, v_type_2726_, v_k_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__0(lean_object* v_a_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_nat_to_int(v_a_2734_);
return v___x_2735_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0));
v___x_2738_ = l_Lean_stringToMessageData(v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(lean_object* v_snd_2739_, lean_object* v_a_2740_, lean_object* v_____r_2741_, lean_object* v_fType_2742_, lean_object* v_j_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
if (lean_obj_tag(v_fType_2742_) == 7)
{
lean_object* v_body_2749_; uint8_t v_binderInfo_2750_; uint8_t v___x_2751_; 
v_body_2749_ = lean_ctor_get(v_fType_2742_, 2);
lean_inc_ref(v_body_2749_);
v_binderInfo_2750_ = lean_ctor_get_uint8(v_fType_2742_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fType_2742_, 3);
v___x_2751_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec(v_a_2740_);
lean_inc(v_j_2743_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v_j_2743_);
lean_ctor_set(v___x_2752_, 1, v_snd_2739_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_body_2749_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
v___x_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
return v___x_2755_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2756_ = lean_array_push(v_snd_2739_, v_a_2740_);
lean_inc(v_j_2743_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_j_2743_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v_body_2749_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
return v___x_2760_;
}
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v_a_2740_);
v___x_2761_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1);
v___x_2762_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2761_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2772_; 
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; 
v_unused_2773_ = lean_ctor_get(v___x_2762_, 0);
lean_dec(v_unused_2773_);
v___x_2764_ = v___x_2762_;
v_isShared_2765_ = v_isSharedCheck_2772_;
goto v_resetjp_2763_;
}
else
{
lean_dec(v___x_2762_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2772_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
lean_inc(v_j_2743_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_j_2743_);
lean_ctor_set(v___x_2766_, 1, v_snd_2739_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_fType_2742_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2768_);
v___x_2770_ = v___x_2764_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec_ref(v_fType_2742_);
lean_dec(v_snd_2739_);
v_a_2774_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2762_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2762_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___boxed(lean_object* v_snd_2782_, lean_object* v_a_2783_, lean_object* v_____r_2784_, lean_object* v_fType_2785_, lean_object* v_j_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2782_, v_a_2783_, v_____r_2784_, v_fType_2785_, v_j_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v_j_2786_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(lean_object* v_upperBound_2793_, lean_object* v_xs_2794_, lean_object* v_a_2795_, lean_object* v_b_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___y_2803_; uint8_t v___x_2825_; 
v___x_2825_ = lean_nat_dec_lt(v_a_2795_, v_upperBound_2793_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
lean_dec(v_a_2795_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_b_2796_);
return v___x_2826_;
}
else
{
lean_object* v_snd_2827_; lean_object* v_fst_2828_; lean_object* v_fst_2829_; lean_object* v_snd_2830_; uint8_t v___x_2831_; 
v_snd_2827_ = lean_ctor_get(v_b_2796_, 1);
lean_inc(v_snd_2827_);
v_fst_2828_ = lean_ctor_get(v_b_2796_, 0);
lean_inc(v_fst_2828_);
lean_dec_ref(v_b_2796_);
v_fst_2829_ = lean_ctor_get(v_snd_2827_, 0);
lean_inc(v_fst_2829_);
v_snd_2830_ = lean_ctor_get(v_snd_2827_, 1);
lean_inc(v_snd_2830_);
lean_dec(v_snd_2827_);
v___x_2831_ = l_Lean_Expr_isForall(v_fst_2828_);
if (v___x_2831_ == 0)
{
lean_object* v_keyedConfig_2832_; uint8_t v_trackZetaDelta_2833_; lean_object* v_zetaDeltaSet_2834_; lean_object* v_lctx_2835_; lean_object* v_localInstances_2836_; lean_object* v_defEqCtx_x3f_2837_; lean_object* v_synthPendingDepth_2838_; lean_object* v_customCanUnfoldPredicate_x3f_2839_; uint8_t v_univApprox_2840_; uint8_t v_inTypeClassResolution_2841_; uint8_t v_cacheInferType_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_keyedConfig_2832_ = lean_ctor_get(v___y_2797_, 0);
v_trackZetaDelta_2833_ = lean_ctor_get_uint8(v___y_2797_, sizeof(void*)*7);
v_zetaDeltaSet_2834_ = lean_ctor_get(v___y_2797_, 1);
v_lctx_2835_ = lean_ctor_get(v___y_2797_, 2);
v_localInstances_2836_ = lean_ctor_get(v___y_2797_, 3);
v_defEqCtx_x3f_2837_ = lean_ctor_get(v___y_2797_, 4);
v_synthPendingDepth_2838_ = lean_ctor_get(v___y_2797_, 5);
v_customCanUnfoldPredicate_x3f_2839_ = lean_ctor_get(v___y_2797_, 6);
v_univApprox_2840_ = lean_ctor_get_uint8(v___y_2797_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2841_ = lean_ctor_get_uint8(v___y_2797_, sizeof(void*)*7 + 2);
v_cacheInferType_2842_ = lean_ctor_get_uint8(v___y_2797_, sizeof(void*)*7 + 3);
v___x_2843_ = 0;
v___x_2844_ = lean_expr_instantiate_rev_range(v_fst_2828_, v_fst_2829_, v_a_2795_, v_xs_2794_);
lean_dec(v_fst_2829_);
lean_dec(v_fst_2828_);
lean_inc_ref(v_keyedConfig_2832_);
v___x_2845_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2843_, v_keyedConfig_2832_);
lean_inc(v_customCanUnfoldPredicate_x3f_2839_);
lean_inc(v_synthPendingDepth_2838_);
lean_inc(v_defEqCtx_x3f_2837_);
lean_inc_ref(v_localInstances_2836_);
lean_inc_ref(v_lctx_2835_);
lean_inc(v_zetaDeltaSet_2834_);
v___x_2846_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
lean_ctor_set(v___x_2846_, 1, v_zetaDeltaSet_2834_);
lean_ctor_set(v___x_2846_, 2, v_lctx_2835_);
lean_ctor_set(v___x_2846_, 3, v_localInstances_2836_);
lean_ctor_set(v___x_2846_, 4, v_defEqCtx_x3f_2837_);
lean_ctor_set(v___x_2846_, 5, v_synthPendingDepth_2838_);
lean_ctor_set(v___x_2846_, 6, v_customCanUnfoldPredicate_x3f_2839_);
lean_ctor_set_uint8(v___x_2846_, sizeof(void*)*7, v_trackZetaDelta_2833_);
lean_ctor_set_uint8(v___x_2846_, sizeof(void*)*7 + 1, v_univApprox_2840_);
lean_ctor_set_uint8(v___x_2846_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2841_);
lean_ctor_set_uint8(v___x_2846_, sizeof(void*)*7 + 3, v_cacheInferType_2842_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
lean_inc(v___y_2798_);
v___x_2847_ = lean_whnf(v___x_2844_, v___x_2846_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2849_ = lean_box(0);
lean_inc(v_a_2795_);
v___x_2850_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2830_, v_a_2795_, v___x_2849_, v_a_2848_, v_a_2795_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
v___y_2803_ = v___x_2850_;
goto v___jp_2802_;
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_snd_2830_);
lean_dec(v_a_2795_);
v_a_2851_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2847_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2847_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_box(0);
lean_inc(v_a_2795_);
v___x_2860_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2830_, v_a_2795_, v___x_2859_, v_fst_2828_, v_fst_2829_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v_fst_2829_);
v___y_2803_ = v___x_2860_;
goto v___jp_2802_;
}
}
v___jp_2802_:
{
if (lean_obj_tag(v___y_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2816_; 
v_a_2804_ = lean_ctor_get(v___y_2803_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___y_2803_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2806_ = v___y_2803_;
v_isShared_2807_ = v_isSharedCheck_2816_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___y_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2816_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
if (lean_obj_tag(v_a_2804_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; 
lean_dec(v_a_2795_);
v_a_2808_ = lean_ctor_get(v_a_2804_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v_a_2804_, 1);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v_a_2808_);
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_del_object(v___x_2806_);
v_a_2812_ = lean_ctor_get(v_a_2804_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v_a_2804_, 1);
v___x_2813_ = lean_unsigned_to_nat(1u);
v___x_2814_ = lean_nat_add(v_a_2795_, v___x_2813_);
lean_dec(v_a_2795_);
v_a_2795_ = v___x_2814_;
v_b_2796_ = v_a_2812_;
goto _start;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v_a_2795_);
v_a_2817_ = lean_ctor_get(v___y_2803_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___y_2803_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___y_2803_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___y_2803_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object* v_upperBound_2861_, lean_object* v_xs_2862_, lean_object* v_a_2863_, lean_object* v_b_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_2861_, v_xs_2862_, v_a_2863_, v_b_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v_xs_2862_);
lean_dec(v_upperBound_2861_);
return v_res_2870_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2));
v___x_2878_ = l_Lean_stringToMessageData(v___x_2877_);
return v___x_2878_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5(void){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4));
v___x_2881_ = l_Lean_stringToMessageData(v___x_2880_);
return v___x_2881_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_unsigned_to_nat(0u);
v___x_2883_ = lean_nat_to_int(v___x_2882_);
return v___x_2883_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_nat_to_int(v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8));
v___x_2888_ = l_Lean_stringToMessageData(v___x_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object* v_tacticName_2889_, uint8_t v_explicit_2890_, lean_object* v_f_2891_, lean_object* v_xs_2892_, lean_object* v_i_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___y_2900_; lean_object* v_lower_2901_; lean_object* v_upper_2902_; lean_object* v___y_2908_; lean_object* v_lower_2909_; lean_object* v_upper_2910_; 
if (v_explicit_2890_ == 0)
{
lean_object* v___x_2915_; 
lean_inc(v_a_2897_);
lean_inc_ref(v_a_2896_);
lean_inc(v_a_2895_);
lean_inc_ref(v_a_2894_);
lean_inc_ref(v_f_2891_);
v___x_2915_ = lean_infer_type(v_f_2891_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = lean_array_get_size(v_xs_2892_);
v___x_2918_ = lean_unsigned_to_nat(0u);
v___x_2919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1));
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v_a_2916_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v___x_2917_, v_xs_2892_, v___x_2918_, v___x_2920_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v_snd_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2981_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v_snd_2923_ = lean_ctor_get(v_a_2922_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_a_2922_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_a_2922_, 0);
lean_dec(v_unused_2982_);
v___x_2925_ = v_a_2922_;
v_isShared_2926_ = v_isSharedCheck_2981_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_snd_2923_);
lean_dec(v_a_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2981_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_snd_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2979_; 
v_snd_2927_ = lean_ctor_get(v_snd_2923_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_snd_2923_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_snd_2923_, 0);
lean_dec(v_unused_2980_);
v___x_2929_ = v_snd_2923_;
v_isShared_2930_ = v_isSharedCheck_2979_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_snd_2927_);
lean_dec(v_snd_2923_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2979_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___y_2932_; lean_object* v___y_2940_; lean_object* v___x_2966_; lean_object* v___y_2968_; uint8_t v___x_2973_; 
v___x_2966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_2973_ = lean_int_dec_lt(v___x_2966_, v_i_2893_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_array_get_size(v_snd_2927_);
v___x_2975_ = lean_nat_to_int(v___x_2974_);
v___x_2976_ = lean_int_add(v_i_2893_, v___x_2975_);
lean_dec(v___x_2975_);
v___y_2968_ = v___x_2976_;
goto v___jp_2967_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_2978_ = lean_int_sub(v_i_2893_, v___x_2977_);
v___y_2968_ = v___x_2978_;
goto v___jp_2967_;
}
v___jp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v___x_2933_ = lean_nat_abs(v___y_2932_);
lean_dec(v___y_2932_);
v___x_2934_ = lean_array_get(v___x_2918_, v_snd_2927_, v___x_2933_);
lean_dec(v___x_2933_);
lean_dec(v_snd_2927_);
lean_inc(v___x_2934_);
lean_inc_ref(v_xs_2892_);
v___x_2935_ = l_Array_toSubarray___redArg(v_xs_2892_, v___x_2918_, v___x_2934_);
v___x_2936_ = l_Subarray_copy___redArg(v___x_2935_);
v___x_2937_ = l_Lean_mkAppN(v_f_2891_, v___x_2936_);
lean_dec_ref(v___x_2936_);
v___x_2938_ = lean_nat_dec_le(v___x_2934_, v___x_2918_);
if (v___x_2938_ == 0)
{
v___y_2908_ = v___x_2937_;
v_lower_2909_ = v___x_2934_;
v_upper_2910_ = v___x_2917_;
goto v___jp_2907_;
}
else
{
lean_dec(v___x_2934_);
v___y_2908_ = v___x_2937_;
v_lower_2909_ = v___x_2918_;
v_upper_2910_ = v___x_2917_;
goto v___jp_2907_;
}
}
v___jp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2944_; 
lean_dec(v___y_2940_);
v___x_2941_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_2942_ = l_Lean_stringToMessageData(v_tacticName_2889_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 7);
lean_ctor_set(v___x_2929_, 1, v___x_2942_);
lean_ctor_set(v___x_2929_, 0, v___x_2941_);
v___x_2944_ = v___x_2929_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2941_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
if (v_isShared_2926_ == 0)
{
lean_ctor_set_tag(v___x_2925_, 7);
lean_ctor_set(v___x_2925_, 1, v___x_2945_);
lean_ctor_set(v___x_2925_, 0, v___x_2944_);
v___x_2947_ = v___x_2925_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
v___x_2948_ = lean_array_get_size(v_snd_2927_);
lean_dec(v_snd_2927_);
v___x_2949_ = l_Nat_reprFast(v___x_2948_);
v___x_2950_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
v___x_2951_ = l_Lean_MessageData_ofFormat(v___x_2950_);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2947_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5);
v___x_2954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
v___x_2955_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2954_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
}
v___jp_2967_:
{
uint8_t v___x_2969_; 
v___x_2969_ = lean_int_dec_lt(v___y_2968_, v___x_2966_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2970_ = lean_array_get_size(v_snd_2927_);
v___x_2971_ = lean_nat_to_int(v___x_2970_);
v___x_2972_ = lean_int_dec_le(v___x_2971_, v___y_2968_);
lean_dec(v___x_2971_);
if (v___x_2972_ == 0)
{
lean_del_object(v___x_2929_);
lean_del_object(v___x_2925_);
lean_dec_ref(v_tacticName_2889_);
v___y_2932_ = v___y_2968_;
goto v___jp_2931_;
}
else
{
lean_dec_ref(v_xs_2892_);
lean_dec_ref(v_f_2891_);
v___y_2940_ = v___y_2968_;
goto v___jp_2939_;
}
}
else
{
lean_dec_ref(v_xs_2892_);
lean_dec_ref(v_f_2891_);
v___y_2940_ = v___y_2968_;
goto v___jp_2939_;
}
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_xs_2892_);
lean_dec_ref(v_f_2891_);
lean_dec_ref(v_tacticName_2889_);
v_a_2983_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2921_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2921_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v_xs_2892_);
lean_dec_ref(v_f_2891_);
lean_dec_ref(v_tacticName_2889_);
v_a_2991_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2915_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2915_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v___x_2999_; lean_object* v___y_3001_; lean_object* v___y_3009_; lean_object* v___x_3031_; lean_object* v___y_3033_; uint8_t v___x_3038_; 
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3038_ = lean_int_dec_lt(v___x_3031_, v_i_2893_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_array_get_size(v_xs_2892_);
v___x_3040_ = lean_nat_to_int(v___x_3039_);
v___x_3041_ = lean_int_add(v_i_2893_, v___x_3040_);
lean_dec(v___x_3040_);
v___y_3033_ = v___x_3041_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3043_ = lean_int_sub(v_i_2893_, v___x_3042_);
v___y_3033_ = v___x_3043_;
goto v___jp_3032_;
}
v___jp_3000_:
{
lean_object* v_idx_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_idx_3002_ = lean_nat_abs(v___y_3001_);
lean_dec(v___y_3001_);
lean_inc(v_idx_3002_);
lean_inc_ref(v_xs_2892_);
v___x_3003_ = l_Array_toSubarray___redArg(v_xs_2892_, v___x_2999_, v_idx_3002_);
v___x_3004_ = l_Subarray_copy___redArg(v___x_3003_);
v___x_3005_ = l_Lean_mkAppN(v_f_2891_, v___x_3004_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = lean_array_get_size(v_xs_2892_);
v___x_3007_ = lean_nat_dec_le(v_idx_3002_, v___x_2999_);
if (v___x_3007_ == 0)
{
v___y_2900_ = v___x_3005_;
v_lower_2901_ = v_idx_3002_;
v_upper_2902_ = v___x_3006_;
goto v___jp_2899_;
}
else
{
lean_dec(v_idx_3002_);
v___y_2900_ = v___x_3005_;
v_lower_2901_ = v___x_2999_;
v_upper_2902_ = v___x_3006_;
goto v___jp_2899_;
}
}
v___jp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v___y_3009_);
v___x_3010_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3011_ = l_Lean_stringToMessageData(v_tacticName_2889_);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_array_get_size(v_xs_2892_);
lean_dec_ref(v_xs_2892_);
v___x_3016_ = l_Nat_reprFast(v___x_3015_);
v___x_3017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
v___x_3018_ = l_Lean_MessageData_ofFormat(v___x_3017_);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3014_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9);
v___x_3021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3021_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3022_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
v___jp_3032_:
{
uint8_t v___x_3034_; 
v___x_3034_ = lean_int_dec_lt(v___y_3033_, v___x_3031_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3035_ = lean_array_get_size(v_xs_2892_);
v___x_3036_ = lean_nat_to_int(v___x_3035_);
v___x_3037_ = lean_int_dec_le(v___x_3036_, v___y_3033_);
lean_dec(v___x_3036_);
if (v___x_3037_ == 0)
{
lean_dec_ref(v_tacticName_2889_);
v___y_3001_ = v___y_3033_;
goto v___jp_3000_;
}
else
{
lean_dec_ref(v_f_2891_);
v___y_3009_ = v___y_3033_;
goto v___jp_3008_;
}
}
else
{
lean_dec_ref(v_f_2891_);
v___y_3009_ = v___y_3033_;
goto v___jp_3008_;
}
}
}
v___jp_2899_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2903_ = l_Array_toSubarray___redArg(v_xs_2892_, v_lower_2901_, v_upper_2902_);
v___x_2904_ = l_Subarray_copy___redArg(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___y_2900_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
return v___x_2906_;
}
v___jp_2907_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2911_ = l_Array_toSubarray___redArg(v_xs_2892_, v_lower_2909_, v_upper_2910_);
v___x_2912_ = l_Subarray_copy___redArg(v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___y_2908_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object* v_tacticName_3044_, lean_object* v_explicit_3045_, lean_object* v_f_3046_, lean_object* v_xs_3047_, lean_object* v_i_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
uint8_t v_explicit_boxed_3054_; lean_object* v_res_3055_; 
v_explicit_boxed_3054_ = lean_unbox(v_explicit_3045_);
v_res_3055_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3044_, v_explicit_boxed_3054_, v_f_3046_, v_xs_3047_, v_i_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_i_3048_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object* v_upperBound_3056_, lean_object* v_xs_3057_, lean_object* v_inst_3058_, lean_object* v_R_3059_, lean_object* v_a_3060_, lean_object* v_b_3061_, lean_object* v_c_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_3056_, v_xs_3057_, v_a_3060_, v_b_3061_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object* v_upperBound_3069_, lean_object* v_xs_3070_, lean_object* v_inst_3071_, lean_object* v_R_3072_, lean_object* v_a_3073_, lean_object* v_b_3074_, lean_object* v_c_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(v_upperBound_3069_, v_xs_3070_, v_inst_3071_, v_R_3072_, v_a_3073_, v_b_3074_, v_c_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec_ref(v_xs_3070_);
lean_dec(v_upperBound_3069_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object* v_tacticName_3082_, uint8_t v_explicit_3083_, lean_object* v_i_3084_, lean_object* v_mvarId_3085_, lean_object* v_snd_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_, lean_object* v_x_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
if (lean_obj_tag(v_x_3087_) == 5)
{
lean_object* v_fn_3095_; lean_object* v_arg_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_fn_3095_ = lean_ctor_get(v_x_3087_, 0);
lean_inc_ref(v_fn_3095_);
v_arg_3096_ = lean_ctor_get(v_x_3087_, 1);
lean_inc_ref(v_arg_3096_);
lean_dec_ref_known(v_x_3087_, 2);
v___x_3097_ = lean_array_set(v_x_3088_, v_x_3089_, v_arg_3096_);
v___x_3098_ = lean_unsigned_to_nat(1u);
v___x_3099_ = lean_nat_sub(v_x_3089_, v___x_3098_);
lean_dec(v_x_3089_);
v_x_3087_ = v_fn_3095_;
v_x_3088_ = v___x_3097_;
v_x_3089_ = v___x_3099_;
goto _start;
}
else
{
lean_object* v___x_3101_; 
lean_dec(v_x_3089_);
lean_inc_ref(v_tacticName_3082_);
v___x_3101_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3082_, v_explicit_3083_, v_x_3087_, v_x_3088_, v_i_3084_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v_fst_3103_; lean_object* v_snd_3104_; lean_object* v___x_3105_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v_fst_3103_ = lean_ctor_get(v_a_3102_, 0);
lean_inc(v_fst_3103_);
v_snd_3104_ = lean_ctor_get(v_a_3102_, 1);
lean_inc(v_snd_3104_);
lean_dec(v_a_3102_);
lean_inc(v_mvarId_3085_);
v___x_3105_ = l_Lean_MVarId_getTag(v_mvarId_3085_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
lean_inc_ref(v_tacticName_3082_);
v___x_3107_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_3082_, v_a_3106_, v_fst_3103_, v_snd_3104_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v_snd_3109_; lean_object* v_fst_3110_; lean_object* v_fst_3111_; lean_object* v_snd_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3138_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v_snd_3109_ = lean_ctor_get(v_a_3108_, 1);
lean_inc(v_snd_3109_);
v_fst_3110_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_fst_3110_);
lean_dec(v_a_3108_);
v_fst_3111_ = lean_ctor_get(v_snd_3109_, 0);
v_snd_3112_ = lean_ctor_get(v_snd_3109_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_snd_3109_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3114_ = v_snd_3109_;
v_isShared_3115_ = v_isSharedCheck_3138_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_snd_3112_);
lean_inc(v_fst_3111_);
lean_dec(v_snd_3109_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3138_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; 
lean_inc(v_fst_3110_);
v___x_3116_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_3082_, v_snd_3086_, v_fst_3110_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v___x_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref_known(v___x_3116_, 1);
v___x_3117_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_3085_, v_fst_3110_, v___y_3091_);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; 
v_unused_3129_ = lean_ctor_get(v___x_3117_, 0);
lean_dec(v_unused_3129_);
v___x_3119_ = v___x_3117_;
v_isShared_3120_ = v_isSharedCheck_3128_;
goto v_resetjp_3118_;
}
else
{
lean_dec(v___x_3117_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3128_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3121_; lean_object* v___x_3123_; 
v___x_3121_ = lean_array_to_list(v_snd_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set_tag(v___x_3114_, 1);
lean_ctor_set(v___x_3114_, 1, v___x_3121_);
v___x_3123_ = v___x_3114_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_fst_3111_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v___x_3121_);
v___x_3123_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
lean_object* v___x_3125_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3123_);
v___x_3125_ = v___x_3119_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_del_object(v___x_3114_);
lean_dec(v_snd_3112_);
lean_dec(v_fst_3111_);
lean_dec(v_fst_3110_);
lean_dec(v_mvarId_3085_);
v_a_3130_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3116_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3116_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v_snd_3086_);
lean_dec(v_mvarId_3085_);
lean_dec_ref(v_tacticName_3082_);
v_a_3139_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3107_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3107_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_snd_3104_);
lean_dec(v_fst_3103_);
lean_dec_ref(v_snd_3086_);
lean_dec(v_mvarId_3085_);
lean_dec_ref(v_tacticName_3082_);
v_a_3147_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3105_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3105_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v_snd_3086_);
lean_dec(v_mvarId_3085_);
lean_dec_ref(v_tacticName_3082_);
v_a_3155_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3101_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3101_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object* v_tacticName_3163_, lean_object* v_explicit_3164_, lean_object* v_i_3165_, lean_object* v_mvarId_3166_, lean_object* v_snd_3167_, lean_object* v_x_3168_, lean_object* v_x_3169_, lean_object* v_x_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v_explicit_boxed_3176_; lean_object* v_res_3177_; 
v_explicit_boxed_3176_ = lean_unbox(v_explicit_3164_);
v_res_3177_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3163_, v_explicit_boxed_3176_, v_i_3165_, v_mvarId_3166_, v_snd_3167_, v_x_3168_, v_x_3169_, v_x_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v_i_3165_);
return v_res_3177_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = lean_unsigned_to_nat(2u);
v___x_3179_ = lean_nat_to_int(v___x_3178_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3181_ = lean_int_neg(v___x_3180_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2));
v___x_3184_ = l_Lean_stringToMessageData(v___x_3183_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object* v_mvarId_3188_, lean_object* v_tacticName_3189_, uint8_t v_explicit_3190_, lean_object* v_i_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v___x_3197_; 
lean_inc(v_mvarId_3188_);
v___x_3197_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_3188_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v_fst_3199_; lean_object* v_snd_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3259_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v_fst_3199_ = lean_ctor_get(v_a_3198_, 0);
v_snd_3200_ = lean_ctor_get(v_a_3198_, 1);
v_isSharedCheck_3259_ = !lean_is_exclusive(v_a_3198_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3202_ = v_a_3198_;
v_isShared_3203_ = v_isSharedCheck_3259_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snd_3200_);
lean_inc(v_fst_3199_);
lean_dec(v_a_3198_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3259_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v_a_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; uint8_t v___y_3237_; 
v___x_3204_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_3199_, v___y_3193_);
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = l_Lean_Expr_cleanupAnnotations(v_a_3205_);
v___x_3207_ = l_Lean_Expr_isForall(v___x_3206_);
if (v___x_3207_ == 0)
{
uint8_t v___x_3240_; 
lean_del_object(v___x_3202_);
v___x_3240_ = l_Lean_Expr_isApp(v___x_3206_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
lean_dec(v_snd_3200_);
lean_dec(v_mvarId_3188_);
v___x_3241_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3242_ = l_Lean_stringToMessageData(v_tacticName_3189_);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Lean_indentExpr(v___x_3206_);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3247_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3248_;
}
else
{
lean_object* v_dummy_3249_; lean_object* v_nargs_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v_dummy_3249_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_3250_ = l_Lean_Expr_getAppNumArgs(v___x_3206_);
lean_inc(v_nargs_3250_);
v___x_3251_ = lean_mk_array(v_nargs_3250_, v_dummy_3249_);
v___x_3252_ = lean_unsigned_to_nat(1u);
v___x_3253_ = lean_nat_sub(v_nargs_3250_, v___x_3252_);
lean_dec(v_nargs_3250_);
v___x_3254_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3189_, v_explicit_3190_, v_i_3191_, v_mvarId_3188_, v_snd_3200_, v___x_3206_, v___x_3251_, v___x_3253_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
return v___x_3254_;
}
}
else
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3256_ = lean_int_dec_lt(v_i_3191_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3258_ = lean_int_dec_eq(v_i_3191_, v___x_3257_);
v___y_3237_ = v___x_3258_;
goto v___jp_3236_;
}
else
{
v___y_3237_ = v___x_3207_;
goto v___jp_3236_;
}
}
v___jp_3208_:
{
lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3214_ = lean_int_dec_eq(v_i_3191_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3216_ = lean_int_dec_eq(v_i_3191_, v___x_3215_);
v___x_3217_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3189_, v___x_3216_, v_mvarId_3188_, v___x_3206_, v_snd_3200_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
return v___x_3217_;
}
else
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3189_, v___x_3207_, v_mvarId_3188_, v___x_3206_, v_snd_3200_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
return v___x_3218_;
}
}
v___jp_3219_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3220_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3221_ = l_Lean_stringToMessageData(v_tacticName_3189_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set_tag(v___x_3202_, 7);
lean_ctor_set(v___x_3202_, 1, v___x_3221_);
lean_ctor_set(v___x_3202_, 0, v___x_3220_);
v___x_3223_ = v___x_3202_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
v___x_3224_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3225_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
v___jp_3236_:
{
if (v___y_3237_ == 0)
{
lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3238_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3239_ = lean_int_dec_lt(v___x_3238_, v_i_3191_);
if (v___x_3239_ == 0)
{
lean_del_object(v___x_3202_);
v___y_3209_ = v___y_3192_;
v___y_3210_ = v___y_3193_;
v___y_3211_ = v___y_3194_;
v___y_3212_ = v___y_3195_;
goto v___jp_3208_;
}
else
{
lean_dec_ref(v___x_3206_);
lean_dec(v_snd_3200_);
lean_dec(v_mvarId_3188_);
goto v___jp_3219_;
}
}
else
{
lean_dec_ref(v___x_3206_);
lean_dec(v_snd_3200_);
lean_dec(v_mvarId_3188_);
goto v___jp_3219_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v_tacticName_3189_);
lean_dec(v_mvarId_3188_);
v_a_3260_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3197_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3197_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object* v_mvarId_3268_, lean_object* v_tacticName_3269_, lean_object* v_explicit_3270_, lean_object* v_i_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
uint8_t v_explicit_boxed_3277_; lean_object* v_res_3278_; 
v_explicit_boxed_3277_ = lean_unbox(v_explicit_3270_);
v_res_3278_ = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(v_mvarId_3268_, v_tacticName_3269_, v_explicit_boxed_3277_, v_i_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v_i_3271_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object* v_tacticName_3279_, lean_object* v_mvarId_3280_, lean_object* v_i_3281_, uint8_t v_explicit_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; 
v___x_3288_ = lean_box(v_explicit_3282_);
lean_inc(v_mvarId_3280_);
v___f_3289_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3289_, 0, v_mvarId_3280_);
lean_closure_set(v___f_3289_, 1, v_tacticName_3279_);
lean_closure_set(v___f_3289_, 2, v___x_3288_);
lean_closure_set(v___f_3289_, 3, v_i_3281_);
v___x_3290_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_3280_, v___f_3289_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object* v_tacticName_3291_, lean_object* v_mvarId_3292_, lean_object* v_i_3293_, lean_object* v_explicit_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
uint8_t v_explicit_boxed_3300_; lean_object* v_res_3301_; 
v_explicit_boxed_3300_ = lean_unbox(v_explicit_3294_);
v_res_3301_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3291_, v_mvarId_3292_, v_i_3293_, v_explicit_boxed_3300_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object* v_tacticName_3302_, lean_object* v_i_3303_, uint8_t v_explicit_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3312_ = lean_int_dec_eq(v_i_3303_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v___x_3315_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3302_, v_a_3314_, v_i_3303_, v_explicit_3304_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3317_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3315_, 1);
v___x_3317_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3316_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
return v___x_3317_;
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
v_a_3318_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3315_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3315_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_i_3303_);
lean_dec_ref(v_tacticName_3302_);
v_a_3326_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3313_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3313_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v___x_3334_; 
lean_dec(v_i_3303_);
lean_dec_ref(v_tacticName_3302_);
v___x_3334_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
v___x_3336_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_a_3335_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
lean_dec_ref_known(v___x_3336_, 1);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v_a_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3339_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
return v___x_3340_;
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
v_a_3341_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3336_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3336_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3334_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3334_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object* v_tacticName_3357_, lean_object* v_i_3358_, lean_object* v_explicit_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
uint8_t v_explicit_boxed_3366_; lean_object* v_res_3367_; 
v_explicit_boxed_3366_ = lean_unbox(v_explicit_3359_);
v_res_3367_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3357_, v_i_3358_, v_explicit_boxed_3366_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object* v_tacticName_3368_, lean_object* v_i_3369_, uint8_t v_explicit_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3368_, v_i_3369_, v_explicit_3370_, v_a_3372_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object* v_tacticName_3381_, lean_object* v_i_3382_, lean_object* v_explicit_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
uint8_t v_explicit_boxed_3393_; lean_object* v_res_3394_; 
v_explicit_boxed_3393_ = lean_unbox(v_explicit_3383_);
v_res_3394_ = l_Lean_Elab_Tactic_Conv_evalArg(v_tacticName_3381_, v_i_3382_, v_explicit_boxed_3393_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
return v_res_3394_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = lean_box(0);
v___x_3396_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v___x_3395_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg(){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3399_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0);
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object* v_00_u03b1_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object* v_00_u03b1_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(v_00_u03b1_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object* v_stx_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; uint8_t v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___x_3476_; uint8_t v___x_3477_; 
v___x_3452_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_3476_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
lean_inc(v_stx_3442_);
v___x_3477_ = l_Lean_Syntax_isOfKind(v_stx_3442_, v___x_3476_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; 
lean_dec(v_stx_3442_);
v___x_3478_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___y_3482_; lean_object* v_neg_x3f_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v___x_3479_ = lean_unsigned_to_nat(1u);
v___x_3480_ = l_Lean_Syntax_getArg(v_stx_3442_, v___x_3479_);
lean_dec(v_stx_3442_);
v___x_3500_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__5));
lean_inc(v___x_3480_);
v___x_3501_ = l_Lean_Syntax_isOfKind(v___x_3480_, v___x_3500_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; 
lean_dec(v___x_3480_);
v___x_3502_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3502_;
}
else
{
lean_object* v___x_3503_; lean_object* v_tk_x3f_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3503_ = lean_unsigned_to_nat(0u);
v___x_3521_ = l_Lean_Syntax_getArg(v___x_3480_, v___x_3503_);
v___x_3522_ = l_Lean_Syntax_isNone(v___x_3521_);
if (v___x_3522_ == 0)
{
uint8_t v___x_3523_; 
lean_inc(v___x_3521_);
v___x_3523_ = l_Lean_Syntax_matchesNull(v___x_3521_, v___x_3479_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3524_; 
lean_dec(v___x_3521_);
lean_dec(v___x_3480_);
v___x_3524_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3524_;
}
else
{
lean_object* v_tk_x3f_3525_; lean_object* v___x_3526_; 
v_tk_x3f_3525_ = l_Lean_Syntax_getArg(v___x_3521_, v___x_3503_);
lean_dec(v___x_3521_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_tk_x3f_3525_);
v_tk_x3f_3505_ = v___x_3526_;
v___y_3506_ = v_a_3443_;
v___y_3507_ = v_a_3444_;
v___y_3508_ = v_a_3445_;
v___y_3509_ = v_a_3446_;
v___y_3510_ = v_a_3447_;
v___y_3511_ = v_a_3448_;
v___y_3512_ = v_a_3449_;
v___y_3513_ = v_a_3450_;
goto v___jp_3504_;
}
}
else
{
lean_object* v___x_3527_; 
lean_dec(v___x_3521_);
v___x_3527_ = lean_box(0);
v_tk_x3f_3505_ = v___x_3527_;
v___y_3506_ = v_a_3443_;
v___y_3507_ = v_a_3444_;
v___y_3508_ = v_a_3445_;
v___y_3509_ = v_a_3446_;
v___y_3510_ = v_a_3447_;
v___y_3511_ = v_a_3448_;
v___y_3512_ = v_a_3449_;
v___y_3513_ = v_a_3450_;
goto v___jp_3504_;
}
v___jp_3504_:
{
lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3514_ = l_Lean_Syntax_getArg(v___x_3480_, v___x_3479_);
v___x_3515_ = l_Lean_Syntax_isNone(v___x_3514_);
if (v___x_3515_ == 0)
{
uint8_t v___x_3516_; 
lean_inc(v___x_3514_);
v___x_3516_ = l_Lean_Syntax_matchesNull(v___x_3514_, v___x_3479_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_dec(v___x_3514_);
lean_dec(v_tk_x3f_3505_);
lean_dec(v___x_3480_);
v___x_3517_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3517_;
}
else
{
lean_object* v_neg_x3f_3518_; lean_object* v___x_3519_; 
v_neg_x3f_3518_ = l_Lean_Syntax_getArg(v___x_3514_, v___x_3503_);
lean_dec(v___x_3514_);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_neg_x3f_3518_);
v___y_3482_ = v_tk_x3f_3505_;
v_neg_x3f_3483_ = v___x_3519_;
v___y_3484_ = v___y_3506_;
v___y_3485_ = v___y_3507_;
v___y_3486_ = v___y_3508_;
v___y_3487_ = v___y_3509_;
v___y_3488_ = v___y_3510_;
v___y_3489_ = v___y_3511_;
v___y_3490_ = v___y_3512_;
v___y_3491_ = v___y_3513_;
goto v___jp_3481_;
}
}
else
{
lean_object* v___x_3520_; 
lean_dec(v___x_3514_);
v___x_3520_ = lean_box(0);
v___y_3482_ = v_tk_x3f_3505_;
v_neg_x3f_3483_ = v___x_3520_;
v___y_3484_ = v___y_3506_;
v___y_3485_ = v___y_3507_;
v___y_3486_ = v___y_3508_;
v___y_3487_ = v___y_3509_;
v___y_3488_ = v___y_3510_;
v___y_3489_ = v___y_3511_;
v___y_3490_ = v___y_3512_;
v___y_3491_ = v___y_3513_;
goto v___jp_3481_;
}
}
}
v___jp_3481_:
{
lean_object* v___x_3492_; lean_object* v_i_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; 
v___x_3492_ = lean_unsigned_to_nat(2u);
v_i_3493_ = l_Lean_Syntax_getArg(v___x_3480_, v___x_3492_);
lean_dec(v___x_3480_);
v___x_3494_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__3));
lean_inc(v_i_3493_);
v___x_3495_ = l_Lean_Syntax_isOfKind(v_i_3493_, v___x_3494_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; 
lean_dec(v_i_3493_);
lean_dec(v_neg_x3f_3483_);
lean_dec(v___y_3482_);
v___x_3496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3496_;
}
else
{
if (lean_obj_tag(v_neg_x3f_3483_) == 0)
{
v___y_3466_ = v___y_3485_;
v___y_3467_ = v___y_3482_;
v___y_3468_ = v_i_3493_;
v___y_3469_ = v___x_3495_;
v___y_3470_ = v___y_3488_;
v___y_3471_ = v___y_3489_;
v___y_3472_ = v___y_3490_;
v___y_3473_ = v___y_3491_;
goto v___jp_3465_;
}
else
{
lean_dec_ref_known(v_neg_x3f_3483_, 1);
if (v___x_3495_ == 0)
{
v___y_3466_ = v___y_3485_;
v___y_3467_ = v___y_3482_;
v___y_3468_ = v_i_3493_;
v___y_3469_ = v___x_3495_;
v___y_3470_ = v___y_3488_;
v___y_3471_ = v___y_3489_;
v___y_3472_ = v___y_3490_;
v___y_3473_ = v___y_3491_;
goto v___jp_3465_;
}
else
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3497_ = l_Lean_TSyntax_getNat(v_i_3493_);
lean_dec(v_i_3493_);
v___x_3498_ = lean_nat_to_int(v___x_3497_);
v___x_3499_ = lean_int_neg(v___x_3498_);
lean_dec(v___x_3498_);
v___y_3454_ = v___y_3485_;
v___y_3455_ = v___y_3482_;
v___y_3456_ = v___x_3495_;
v___y_3457_ = v___y_3488_;
v___y_3458_ = v___y_3489_;
v___y_3459_ = v___y_3491_;
v___y_3460_ = v___y_3490_;
v___y_3461_ = v___x_3499_;
goto v___jp_3453_;
}
}
}
}
}
v___jp_3453_:
{
if (lean_obj_tag(v___y_3455_) == 0)
{
uint8_t v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = 0;
v___x_3463_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3452_, v___y_3461_, v___x_3462_, v___y_3454_, v___y_3457_, v___y_3458_, v___y_3460_, v___y_3459_);
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; 
lean_dec_ref_known(v___y_3455_, 1);
v___x_3464_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3452_, v___y_3461_, v___y_3456_, v___y_3454_, v___y_3457_, v___y_3458_, v___y_3460_, v___y_3459_);
return v___x_3464_;
}
}
v___jp_3465_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = l_Lean_TSyntax_getNat(v___y_3468_);
lean_dec(v___y_3468_);
v___x_3475_ = lean_nat_to_int(v___x_3474_);
v___y_3454_ = v___y_3466_;
v___y_3455_ = v___y_3467_;
v___y_3456_ = v___y_3469_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___y_3471_;
v___y_3459_ = v___y_3473_;
v___y_3460_ = v___y_3472_;
v___y_3461_ = v___x_3475_;
goto v___jp_3453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object* v_stx_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Elab_Tactic_Conv_elabArg(v_stx_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1(){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3547_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3548_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
v___x_3549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1));
v___x_3550_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_elabArg___boxed), 10, 0);
v___x_3551_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3547_, v___x_3548_, v___x_3549_, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; lean_object* v___x_3564_; 
v___x_3561_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0));
v___x_3562_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3563_ = 0;
v___x_3564_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3561_, v___x_3562_, v___x_3563_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object* v_x_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3574_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object* v_x_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_Elab_Tactic_Conv_evalLhs(v_x_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec_ref(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_x_3583_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1(){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3608_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0));
v___x_3610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3611_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLhs___boxed), 10, 0);
v___x_3612_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3608_, v___x_3609_, v___x_3610_, v___x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object* v_a_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3(){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3642_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6));
v___x_3643_ = l_Lean_addBuiltinDeclarationRanges(v___x_3641_, v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
return v_res_3645_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3648_ = lean_int_neg(v___x_3647_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; 
v___x_3655_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0));
v___x_3656_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1, &l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1);
v___x_3657_ = 0;
v___x_3658_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3655_, v___x_3656_, v___x_3657_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object* v_x_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3668_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object* v_x_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_Elab_Tactic_Conv_evalRhs(v_x_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec(v_x_3677_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1(){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3702_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3703_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0));
v___x_3704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3705_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRhs___boxed), 10, 0);
v___x_3706_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3702_, v___x_3703_, v___x_3704_, v___x_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object* v_a_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3(){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6));
v___x_3737_ = l_Lean_addBuiltinDeclarationRanges(v___x_3735_, v___x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object* v_e_3740_, lean_object* v___y_3741_){
_start:
{
uint8_t v___x_3743_; 
v___x_3743_ = l_Lean_Expr_hasMVar(v_e_3740_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_e_3740_);
return v___x_3744_;
}
else
{
lean_object* v___x_3745_; lean_object* v_mctx_3746_; lean_object* v___x_3747_; lean_object* v_fst_3748_; lean_object* v_snd_3749_; lean_object* v___x_3750_; lean_object* v_cache_3751_; lean_object* v_zetaDeltaFVarIds_3752_; lean_object* v_postponed_3753_; lean_object* v_diag_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3763_; 
v___x_3745_ = lean_st_ref_get(v___y_3741_);
v_mctx_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc_ref(v_mctx_3746_);
lean_dec(v___x_3745_);
v___x_3747_ = l_Lean_instantiateMVarsCore(v_mctx_3746_, v_e_3740_);
v_fst_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_fst_3748_);
v_snd_3749_ = lean_ctor_get(v___x_3747_, 1);
lean_inc(v_snd_3749_);
lean_dec_ref(v___x_3747_);
v___x_3750_ = lean_st_ref_take(v___y_3741_);
v_cache_3751_ = lean_ctor_get(v___x_3750_, 1);
v_zetaDeltaFVarIds_3752_ = lean_ctor_get(v___x_3750_, 2);
v_postponed_3753_ = lean_ctor_get(v___x_3750_, 3);
v_diag_3754_ = lean_ctor_get(v___x_3750_, 4);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; 
v_unused_3764_ = lean_ctor_get(v___x_3750_, 0);
lean_dec(v_unused_3764_);
v___x_3756_ = v___x_3750_;
v_isShared_3757_ = v_isSharedCheck_3763_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_diag_3754_);
lean_inc(v_postponed_3753_);
lean_inc(v_zetaDeltaFVarIds_3752_);
lean_inc(v_cache_3751_);
lean_dec(v___x_3750_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3763_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 0, v_snd_3749_);
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_snd_3749_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_cache_3751_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_zetaDeltaFVarIds_3752_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_postponed_3753_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_diag_3754_);
v___x_3759_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_st_ref_put(v___y_3741_, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_fst_3748_);
return v___x_3761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object* v_e_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3765_, v___y_3766_);
lean_dec(v___y_3766_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object* v_e_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3769_, v___y_3775_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object* v_e_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(v_e_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object* v_x_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; 
lean_inc(v___y_3795_);
lean_inc_ref(v___y_3794_);
lean_inc(v___y_3793_);
lean_inc_ref(v___y_3792_);
v___x_3801_ = lean_apply_9(v_x_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, lean_box(0));
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object* v_x_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(v_x_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object* v_mvarId_3813_, lean_object* v_x_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___f_3824_; lean_object* v___x_3825_; 
lean_inc(v___y_3818_);
lean_inc_ref(v___y_3817_);
lean_inc(v___y_3816_);
lean_inc_ref(v___y_3815_);
v___f_3824_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3824_, 0, v_x_3814_);
lean_closure_set(v___f_3824_, 1, v___y_3815_);
lean_closure_set(v___f_3824_, 2, v___y_3816_);
lean_closure_set(v___f_3824_, 3, v___y_3817_);
lean_closure_set(v___f_3824_, 4, v___y_3818_);
v___x_3825_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3813_, v___f_3824_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
if (lean_obj_tag(v___x_3825_) == 0)
{
return v___x_3825_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object* v_mvarId_3834_, lean_object* v_x_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3834_, v_x_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object* v_00_u03b1_3846_, lean_object* v_mvarId_3847_, lean_object* v_x_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3847_, v_x_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object* v_00_u03b1_3859_, lean_object* v_mvarId_3860_, lean_object* v_x_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(v_00_u03b1_3859_, v_mvarId_3860_, v_x_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object* v_msg_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_ref_3878_; lean_object* v___x_3879_; lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3888_; 
v_ref_3878_ = lean_ctor_get(v___y_3875_, 5);
v___x_3879_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3882_ = v___x_3879_;
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3879_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3888_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
lean_inc(v_ref_3878_);
v___x_3884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3884_, 0, v_ref_3878_);
lean_ctor_set(v___x_3884_, 1, v_a_3880_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set_tag(v___x_3882_, 1);
lean_ctor_set(v___x_3882_, 0, v___x_3884_);
v___x_3886_ = v___x_3882_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object* v_msg_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object* v_mvarId_3896_, lean_object* v_val_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; lean_object* v_mctx_3901_; lean_object* v_cache_3902_; lean_object* v_zetaDeltaFVarIds_3903_; lean_object* v_postponed_3904_; lean_object* v_diag_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3934_; 
v___x_3900_ = lean_st_ref_take(v___y_3898_);
v_mctx_3901_ = lean_ctor_get(v___x_3900_, 0);
v_cache_3902_ = lean_ctor_get(v___x_3900_, 1);
v_zetaDeltaFVarIds_3903_ = lean_ctor_get(v___x_3900_, 2);
v_postponed_3904_ = lean_ctor_get(v___x_3900_, 3);
v_diag_3905_ = lean_ctor_get(v___x_3900_, 4);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3907_ = v___x_3900_;
v_isShared_3908_ = v_isSharedCheck_3934_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_diag_3905_);
lean_inc(v_postponed_3904_);
lean_inc(v_zetaDeltaFVarIds_3903_);
lean_inc(v_cache_3902_);
lean_inc(v_mctx_3901_);
lean_dec(v___x_3900_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3934_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v_depth_3909_; lean_object* v_levelAssignDepth_3910_; lean_object* v_lmvarCounter_3911_; lean_object* v_mvarCounter_3912_; lean_object* v_lDecls_3913_; lean_object* v_decls_3914_; lean_object* v_userNames_3915_; lean_object* v_lAssignment_3916_; lean_object* v_eAssignment_3917_; lean_object* v_dAssignment_3918_; lean_object* v_instanceTypedMVars_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3933_; 
v_depth_3909_ = lean_ctor_get(v_mctx_3901_, 0);
v_levelAssignDepth_3910_ = lean_ctor_get(v_mctx_3901_, 1);
v_lmvarCounter_3911_ = lean_ctor_get(v_mctx_3901_, 2);
v_mvarCounter_3912_ = lean_ctor_get(v_mctx_3901_, 3);
v_lDecls_3913_ = lean_ctor_get(v_mctx_3901_, 4);
v_decls_3914_ = lean_ctor_get(v_mctx_3901_, 5);
v_userNames_3915_ = lean_ctor_get(v_mctx_3901_, 6);
v_lAssignment_3916_ = lean_ctor_get(v_mctx_3901_, 7);
v_eAssignment_3917_ = lean_ctor_get(v_mctx_3901_, 8);
v_dAssignment_3918_ = lean_ctor_get(v_mctx_3901_, 9);
v_instanceTypedMVars_3919_ = lean_ctor_get(v_mctx_3901_, 10);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_mctx_3901_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3921_ = v_mctx_3901_;
v_isShared_3922_ = v_isSharedCheck_3933_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_instanceTypedMVars_3919_);
lean_inc(v_dAssignment_3918_);
lean_inc(v_eAssignment_3917_);
lean_inc(v_lAssignment_3916_);
lean_inc(v_userNames_3915_);
lean_inc(v_decls_3914_);
lean_inc(v_lDecls_3913_);
lean_inc(v_mvarCounter_3912_);
lean_inc(v_lmvarCounter_3911_);
lean_inc(v_levelAssignDepth_3910_);
lean_inc(v_depth_3909_);
lean_dec(v_mctx_3901_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3933_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
v___x_3923_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_3917_, v_mvarId_3896_, v_val_3897_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 8, v___x_3923_);
v___x_3925_ = v___x_3921_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_depth_3909_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_levelAssignDepth_3910_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_lmvarCounter_3911_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_mvarCounter_3912_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v_lDecls_3913_);
lean_ctor_set(v_reuseFailAlloc_3932_, 5, v_decls_3914_);
lean_ctor_set(v_reuseFailAlloc_3932_, 6, v_userNames_3915_);
lean_ctor_set(v_reuseFailAlloc_3932_, 7, v_lAssignment_3916_);
lean_ctor_set(v_reuseFailAlloc_3932_, 8, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3932_, 9, v_dAssignment_3918_);
lean_ctor_set(v_reuseFailAlloc_3932_, 10, v_instanceTypedMVars_3919_);
v___x_3925_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3927_; 
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3925_);
v___x_3927_ = v___x_3907_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_cache_3902_);
lean_ctor_set(v_reuseFailAlloc_3931_, 2, v_zetaDeltaFVarIds_3903_);
lean_ctor_set(v_reuseFailAlloc_3931_, 3, v_postponed_3904_);
lean_ctor_set(v_reuseFailAlloc_3931_, 4, v_diag_3905_);
v___x_3927_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3928_ = lean_st_ref_put(v___y_3898_, v___x_3927_);
v___x_3929_ = lean_box(0);
v___x_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
return v___x_3930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object* v_mvarId_3935_, lean_object* v_val_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_3935_, v_val_3936_, v___y_3937_);
lean_dec(v___y_3937_);
return v_res_3939_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1));
v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object* v_a_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v___x_3954_; 
lean_inc(v_a_3944_);
v___x_3954_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_3944_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v_fst_3956_; lean_object* v_snd_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_4009_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v_fst_3956_ = lean_ctor_get(v_a_3955_, 0);
v_snd_3957_ = lean_ctor_get(v_a_3955_, 1);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_a_3955_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3959_ = v_a_3955_;
v_isShared_3960_ = v_isSharedCheck_4009_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_snd_3957_);
lean_inc(v_fst_3956_);
lean_dec(v_a_3955_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_4009_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v_a_3962_; lean_object* v___x_3963_; 
v___x_3961_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_fst_3956_, v___y_3950_);
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref(v___x_3961_);
v___x_3963_ = l_Lean_Expr_cleanupAnnotations(v_a_3962_);
if (lean_obj_tag(v___x_3963_) == 5)
{
lean_object* v_fn_3964_; lean_object* v_arg_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_del_object(v___x_3959_);
v_fn_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc_ref(v_fn_3964_);
v_arg_3965_ = lean_ctor_get(v___x_3963_, 1);
lean_inc_ref(v_arg_3965_);
lean_dec_ref_known(v___x_3963_, 2);
v___x_3966_ = lean_box(0);
v___x_3967_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fn_3964_, v___x_3966_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v_fst_3969_; lean_object* v_snd_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3994_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v___x_3967_, 1);
v_fst_3969_ = lean_ctor_get(v_a_3968_, 0);
v_snd_3970_ = lean_ctor_get(v_a_3968_, 1);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_a_3968_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3972_ = v_a_3968_;
v_isShared_3973_ = v_isSharedCheck_3994_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_snd_3970_);
lean_inc(v_fst_3969_);
lean_dec(v_a_3968_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3994_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; 
lean_inc_ref(v_arg_3965_);
lean_inc(v_snd_3970_);
v___x_3974_ = l_Lean_Meta_mkCongrFun(v_snd_3970_, v_arg_3965_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v___x_3976_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_a_3944_, v_a_3975_, v___y_3950_);
lean_dec_ref(v___x_3976_);
v___x_3977_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0));
v___x_3978_ = l_Lean_Expr_app___override(v_fst_3969_, v_arg_3965_);
v___x_3979_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_3977_, v_snd_3957_, v___x_3978_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3983_; 
lean_dec_ref_known(v___x_3979_, 1);
v___x_3980_ = l_Lean_Expr_mvarId_x21(v_snd_3970_);
lean_dec(v_snd_3970_);
v___x_3981_ = lean_box(0);
if (v_isShared_3973_ == 0)
{
lean_ctor_set_tag(v___x_3972_, 1);
lean_ctor_set(v___x_3972_, 1, v___x_3981_);
lean_ctor_set(v___x_3972_, 0, v___x_3980_);
v___x_3983_ = v___x_3972_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v___x_3981_);
v___x_3983_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
lean_object* v___x_3984_; 
v___x_3984_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3983_, v___y_3946_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_3984_;
}
}
else
{
lean_del_object(v___x_3972_);
lean_dec(v_snd_3970_);
return v___x_3979_;
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_del_object(v___x_3972_);
lean_dec(v_snd_3970_);
lean_dec(v_fst_3969_);
lean_dec_ref(v_arg_3965_);
lean_dec(v_snd_3957_);
lean_dec(v_a_3944_);
v_a_3986_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3974_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3974_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec_ref(v_arg_3965_);
lean_dec(v_snd_3957_);
lean_dec(v_a_3944_);
v_a_3995_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3967_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3967_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
else
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4006_; 
lean_dec(v_snd_3957_);
lean_dec(v_a_3944_);
v___x_4003_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2);
v___x_4004_ = l_Lean_indentExpr(v___x_3963_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set_tag(v___x_3959_, 7);
lean_ctor_set(v___x_3959_, 1, v___x_4004_);
lean_ctor_set(v___x_3959_, 0, v___x_4003_);
v___x_4006_ = v___x_3959_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4003_);
lean_ctor_set(v_reuseFailAlloc_4008_, 1, v___x_4004_);
v___x_4006_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v___x_4006_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_4007_;
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v_a_3944_);
v_a_4010_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3954_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3954_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object* v_a_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(v_a_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4030_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___f_4040_; lean_object* v___x_4041_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc_n(v_a_4039_, 2);
lean_dec_ref_known(v___x_4038_, 1);
v___f_4040_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4040_, 0, v_a_4039_);
v___x_4041_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_a_4039_, v___f_4040_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_a_4042_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4038_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4038_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object* v_x_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object* v_x_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_Elab_Tactic_Conv_evalFun(v_x_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
lean_dec(v_x_4071_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object* v_mvarId_4082_, lean_object* v_val_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_4082_, v_val_4083_, v___y_4089_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object* v_mvarId_4094_, lean_object* v_val_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(v_mvarId_4094_, v_val_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object* v_00_u03b1_4106_, lean_object* v_msg_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_4107_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object* v_00_u03b1_4118_, lean_object* v_msg_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(v_00_u03b1_4118_, v_msg_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1(){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4144_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0));
v___x_4146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4147_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___boxed), 10, 0);
v___x_4148_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4144_, v___x_4145_, v___x_4146_, v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3(){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6));
v___x_4179_ = l_Lean_addBuiltinDeclarationRanges(v___x_4177_, v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object* v_a_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
return v_res_4181_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4183_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0));
v___x_4184_ = l_Lean_stringToMessageData(v___x_4183_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object* v___x_4185_, lean_object* v_declName_4186_, lean_object* v_type_4187_, lean_object* v_value_4188_, lean_object* v_rhs_4189_, lean_object* v_a_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_inc_ref(v_a_4190_);
v___x_4196_ = l_Lean_Expr_app___override(v___x_4185_, v_a_4190_);
lean_inc(v___y_4194_);
lean_inc_ref(v___y_4193_);
lean_inc(v___y_4192_);
lean_inc_ref(v___y_4191_);
v___x_4197_ = lean_infer_type(v___x_4196_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; uint8_t v___x_4203_; uint8_t v___x_4204_; lean_object* v___x_4205_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc_n(v_a_4198_, 2);
lean_dec_ref_known(v___x_4197_, 1);
v___x_4199_ = lean_unsigned_to_nat(1u);
v___x_4200_ = lean_mk_empty_array_with_capacity(v___x_4199_);
v___x_4201_ = lean_array_push(v___x_4200_, v_a_4190_);
v___x_4202_ = 0;
v___x_4203_ = 1;
v___x_4204_ = 1;
v___x_4205_ = l_Lean_Meta_mkLambdaFVars(v___x_4201_, v_a_4198_, v___x_4202_, v___x_4203_, v___x_4202_, v___x_4203_, v___x_4204_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
lean_inc(v_a_4198_);
v___x_4207_ = l_Lean_Meta_getLevel(v_a_4198_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
v___x_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4209_, 0, v_a_4198_);
v___x_4210_ = 0;
v___x_4211_ = lean_box(0);
v___x_4212_ = l_Lean_Meta_mkFreshExprMVar(v___x_4209_, v___x_4210_, v___x_4211_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___x_4214_ = l_Lean_Meta_mkLambdaFVars(v___x_4201_, v_a_4213_, v___x_4202_, v___x_4203_, v___x_4202_, v___x_4203_, v___x_4204_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
lean_dec_ref(v___x_4201_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4248_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4248_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4248_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = l_Lean_Expr_bindingBody_x21(v_a_4215_);
v___x_4226_ = l_Lean_Expr_letE___override(v_declName_4186_, v_type_4187_, v_value_4188_, v___x_4225_, v___x_4202_);
v___x_4227_ = l_Lean_Meta_isExprDefEq(v_rhs_4189_, v___x_4226_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; uint8_t v___x_4229_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = lean_unbox(v_a_4228_);
lean_dec(v_a_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_del_object(v___x_4217_);
lean_dec(v_a_4215_);
lean_dec(v_a_4208_);
lean_dec(v_a_4206_);
v___x_4230_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1);
v___x_4231_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4230_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4231_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
else
{
goto v___jp_4219_;
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_del_object(v___x_4217_);
lean_dec(v_a_4215_);
lean_dec(v_a_4208_);
lean_dec(v_a_4206_);
v_a_4240_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4227_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4227_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
v___jp_4219_:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4223_; 
v___x_4220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4220_, 0, v_a_4208_);
lean_ctor_set(v___x_4220_, 1, v_a_4215_);
v___x_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4221_, 0, v_a_4206_);
lean_ctor_set(v___x_4221_, 1, v___x_4220_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4221_);
v___x_4223_ = v___x_4217_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec(v_a_4208_);
lean_dec(v_a_4206_);
lean_dec_ref(v_rhs_4189_);
lean_dec_ref(v_value_4188_);
lean_dec_ref(v_type_4187_);
lean_dec(v_declName_4186_);
v_a_4249_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4214_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4214_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec(v_a_4208_);
lean_dec(v_a_4206_);
lean_dec_ref(v___x_4201_);
lean_dec_ref(v_rhs_4189_);
lean_dec_ref(v_value_4188_);
lean_dec_ref(v_type_4187_);
lean_dec(v_declName_4186_);
v_a_4257_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4212_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4212_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec(v_a_4206_);
lean_dec_ref(v___x_4201_);
lean_dec(v_a_4198_);
lean_dec_ref(v_rhs_4189_);
lean_dec_ref(v_value_4188_);
lean_dec_ref(v_type_4187_);
lean_dec(v_declName_4186_);
v_a_4265_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4207_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4207_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec_ref(v___x_4201_);
lean_dec(v_a_4198_);
lean_dec_ref(v_rhs_4189_);
lean_dec_ref(v_value_4188_);
lean_dec_ref(v_type_4187_);
lean_dec(v_declName_4186_);
v_a_4273_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4205_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4205_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec_ref(v_a_4190_);
lean_dec_ref(v_rhs_4189_);
lean_dec_ref(v_value_4188_);
lean_dec_ref(v_type_4187_);
lean_dec(v_declName_4186_);
v_a_4281_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4197_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4197_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object* v___x_4289_, lean_object* v_declName_4290_, lean_object* v_type_4291_, lean_object* v_value_4292_, lean_object* v_rhs_4293_, lean_object* v_a_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(v___x_4289_, v_declName_4290_, v_type_4291_, v_value_4292_, v_rhs_4293_, v_a_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object* v___x_4301_, lean_object* v_snd_4302_, lean_object* v_x_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4309_ = lean_unsigned_to_nat(1u);
v___x_4310_ = lean_mk_empty_array_with_capacity(v___x_4309_);
v___x_4311_ = lean_array_push(v___x_4310_, v_x_4303_);
lean_inc_ref_n(v___x_4311_, 2);
v___x_4312_ = l_Lean_Expr_beta(v___x_4301_, v___x_4311_);
v___x_4313_ = l_Lean_Expr_beta(v_snd_4302_, v___x_4311_);
v___x_4314_ = l_Lean_Meta_mkEq(v___x_4312_, v___x_4313_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = lean_box(0);
v___x_4317_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4315_, v___x_4316_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; uint8_t v___x_4319_; uint8_t v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc_n(v_a_4318_, 2);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4319_ = 0;
v___x_4320_ = 1;
v___x_4321_ = 1;
v___x_4322_ = l_Lean_Meta_mkLambdaFVars(v___x_4311_, v_a_4318_, v___x_4319_, v___x_4320_, v___x_4319_, v___x_4320_, v___x_4321_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec_ref(v___x_4311_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4332_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4332_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4332_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4330_; 
v___x_4327_ = l_Lean_Expr_mvarId_x21(v_a_4318_);
lean_dec(v_a_4318_);
v___x_4328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4328_, 0, v_a_4323_);
lean_ctor_set(v___x_4328_, 1, v___x_4327_);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 0, v___x_4328_);
v___x_4330_ = v___x_4325_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec(v_a_4318_);
v_a_4333_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4322_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4322_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
else
{
lean_object* v_a_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4348_; 
lean_dec_ref(v___x_4311_);
v_a_4341_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4348_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4348_ == 0)
{
v___x_4343_ = v___x_4317_;
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_a_4341_);
lean_dec(v___x_4317_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4348_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4346_; 
if (v_isShared_4344_ == 0)
{
v___x_4346_ = v___x_4343_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec_ref(v___x_4311_);
v_a_4349_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4314_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4314_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object* v___x_4357_, lean_object* v_snd_4358_, lean_object* v_x_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(v___x_4357_, v_snd_4358_, v_x_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
return v_res_4365_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3(void){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2));
v___x_4371_ = l_Lean_stringToMessageData(v___x_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object* v_mvarId_4372_, lean_object* v_lhs_4373_, lean_object* v_rhs_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_){
_start:
{
if (lean_obj_tag(v_lhs_4373_) == 8)
{
lean_object* v_declName_4380_; lean_object* v_type_4381_; lean_object* v_value_4382_; lean_object* v_body_4383_; lean_object* v___x_4384_; 
v_declName_4380_ = lean_ctor_get(v_lhs_4373_, 0);
lean_inc(v_declName_4380_);
v_type_4381_ = lean_ctor_get(v_lhs_4373_, 1);
lean_inc_ref_n(v_type_4381_, 2);
v_value_4382_ = lean_ctor_get(v_lhs_4373_, 2);
lean_inc_ref(v_value_4382_);
v_body_4383_ = lean_ctor_get(v_lhs_4373_, 3);
lean_inc_ref(v_body_4383_);
lean_dec_ref_known(v_lhs_4373_, 4);
v___x_4384_ = l_Lean_Meta_getLevel(v_type_4381_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; uint8_t v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = 0;
lean_inc_ref(v_type_4381_);
lean_inc(v_declName_4380_);
v___x_4387_ = l_Lean_mkLambda(v_declName_4380_, v___x_4386_, v_type_4381_, v_body_4383_);
lean_inc_ref(v___x_4387_);
v___x_4388_ = l_Lean_Meta_isTypeCorrect(v___x_4387_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___f_4390_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; uint8_t v___x_4467_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
lean_inc_ref(v_value_4382_);
lean_inc_ref(v_type_4381_);
lean_inc(v_declName_4380_);
lean_inc_ref(v___x_4387_);
v___f_4390_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4390_, 0, v___x_4387_);
lean_closure_set(v___f_4390_, 1, v_declName_4380_);
lean_closure_set(v___f_4390_, 2, v_type_4381_);
lean_closure_set(v___f_4390_, 3, v_value_4382_);
lean_closure_set(v___f_4390_, 4, v_rhs_4374_);
v___x_4467_ = lean_unbox(v_a_4389_);
lean_dec(v_a_4389_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec_ref(v___f_4390_);
lean_dec_ref(v___x_4387_);
lean_dec(v_a_4385_);
lean_dec_ref(v_value_4382_);
lean_dec_ref(v_type_4381_);
lean_dec(v_declName_4380_);
lean_dec(v_mvarId_4372_);
v___x_4468_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3);
v___x_4469_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4468_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_);
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4469_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4469_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
else
{
v___y_4392_ = v_a_4375_;
v___y_4393_ = v_a_4376_;
v___y_4394_ = v_a_4377_;
v___y_4395_ = v_a_4378_;
goto v___jp_4391_;
}
v___jp_4391_:
{
lean_object* v___x_4396_; 
lean_inc_ref(v_type_4381_);
lean_inc(v_declName_4380_);
v___x_4396_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4380_, v_type_4381_, v___f_4390_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v_snd_4398_; lean_object* v_fst_4399_; lean_object* v_fst_4400_; lean_object* v_snd_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4458_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
v_snd_4398_ = lean_ctor_get(v_a_4397_, 1);
lean_inc(v_snd_4398_);
v_fst_4399_ = lean_ctor_get(v_a_4397_, 0);
lean_inc(v_fst_4399_);
lean_dec(v_a_4397_);
v_fst_4400_ = lean_ctor_get(v_snd_4398_, 0);
v_snd_4401_ = lean_ctor_get(v_snd_4398_, 1);
v_isSharedCheck_4458_ = !lean_is_exclusive(v_snd_4398_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4403_ = v_snd_4398_;
v_isShared_4404_ = v_isSharedCheck_4458_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_snd_4401_);
lean_inc(v_fst_4400_);
lean_dec(v_snd_4398_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4458_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___f_4405_; lean_object* v___x_4406_; 
lean_inc(v_snd_4401_);
lean_inc_ref(v___x_4387_);
v___f_4405_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4405_, 0, v___x_4387_);
lean_closure_set(v___f_4405_, 1, v_snd_4401_);
lean_inc_ref(v_type_4381_);
v___x_4406_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4380_, v_type_4381_, v___f_4405_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v_fst_4408_; lean_object* v_snd_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4449_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v_fst_4408_ = lean_ctor_get(v_a_4407_, 0);
v_snd_4409_ = lean_ctor_get(v_a_4407_, 1);
v_isSharedCheck_4449_ = !lean_is_exclusive(v_a_4407_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4411_ = v_a_4407_;
v_isShared_4412_ = v_isSharedCheck_4449_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_snd_4409_);
lean_inc(v_fst_4408_);
lean_dec(v_a_4407_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4449_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4416_; 
v___x_4413_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1));
v___x_4414_ = lean_box(0);
if (v_isShared_4412_ == 0)
{
lean_ctor_set_tag(v___x_4411_, 1);
lean_ctor_set(v___x_4411_, 1, v___x_4414_);
lean_ctor_set(v___x_4411_, 0, v_fst_4400_);
v___x_4416_ = v___x_4411_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_fst_4400_);
lean_ctor_set(v_reuseFailAlloc_4448_, 1, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4418_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set_tag(v___x_4403_, 1);
lean_ctor_set(v___x_4403_, 1, v___x_4416_);
lean_ctor_set(v___x_4403_, 0, v_a_4385_);
v___x_4418_ = v___x_4403_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4385_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4445_; 
v___x_4419_ = l_Lean_mkConst(v___x_4413_, v___x_4418_);
v___x_4420_ = l_Lean_mkApp6(v___x_4419_, v_type_4381_, v_fst_4399_, v___x_4387_, v_snd_4401_, v_value_4382_, v_fst_4408_);
v___x_4421_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4372_, v___x_4420_, v___y_4393_);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4445_ == 0)
{
lean_object* v_unused_4446_; 
v_unused_4446_ = lean_ctor_get(v___x_4421_, 0);
lean_dec(v_unused_4446_);
v___x_4423_ = v___x_4421_;
v_isShared_4424_ = v_isSharedCheck_4445_;
goto v_resetjp_4422_;
}
else
{
lean_dec(v___x_4421_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4445_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; 
v___x_4425_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4409_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4436_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4428_ = v___x_4425_;
v_isShared_4429_ = v_isSharedCheck_4436_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4436_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4424_ == 0)
{
lean_ctor_set_tag(v___x_4423_, 1);
lean_ctor_set(v___x_4423_, 0, v_a_4426_);
v___x_4431_ = v___x_4423_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
lean_object* v___x_4433_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___x_4431_);
v___x_4433_ = v___x_4428_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_del_object(v___x_4423_);
v_a_4437_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4425_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4425_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
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
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_del_object(v___x_4403_);
lean_dec(v_snd_4401_);
lean_dec(v_fst_4400_);
lean_dec(v_fst_4399_);
lean_dec_ref(v___x_4387_);
lean_dec(v_a_4385_);
lean_dec_ref(v_value_4382_);
lean_dec_ref(v_type_4381_);
lean_dec(v_mvarId_4372_);
v_a_4450_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4406_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4406_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_dec_ref(v___x_4387_);
lean_dec(v_a_4385_);
lean_dec_ref(v_value_4382_);
lean_dec_ref(v_type_4381_);
lean_dec(v_declName_4380_);
lean_dec(v_mvarId_4372_);
v_a_4459_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4396_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4396_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec_ref(v___x_4387_);
lean_dec(v_a_4385_);
lean_dec_ref(v_value_4382_);
lean_dec_ref(v_type_4381_);
lean_dec(v_declName_4380_);
lean_dec_ref(v_rhs_4374_);
lean_dec(v_mvarId_4372_);
v_a_4478_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4388_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4388_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec_ref(v_body_4383_);
lean_dec_ref(v_value_4382_);
lean_dec_ref(v_type_4381_);
lean_dec(v_declName_4380_);
lean_dec_ref(v_rhs_4374_);
lean_dec(v_mvarId_4372_);
v_a_4486_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4384_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4384_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
lean_dec_ref(v_rhs_4374_);
lean_dec_ref(v_lhs_4373_);
lean_dec(v_mvarId_4372_);
v___x_4494_ = lean_box(0);
v___x_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4494_);
return v___x_4495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object* v_mvarId_4496_, lean_object* v_lhs_4497_, lean_object* v_rhs_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4496_, v_lhs_4497_, v_rhs_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object* v_body_4506_, lean_object* v_snd_4507_, lean_object* v_b_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4514_ = lean_expr_instantiate1(v_body_4506_, v_b_4508_);
v___x_4515_ = lean_box(0);
v___x_4516_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_4514_, v___x_4515_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v_fst_4518_; lean_object* v_snd_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4581_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_a_4517_);
lean_dec_ref_known(v___x_4516_, 1);
v_fst_4518_ = lean_ctor_get(v_a_4517_, 0);
v_snd_4519_ = lean_ctor_get(v_a_4517_, 1);
v_isSharedCheck_4581_ = !lean_is_exclusive(v_a_4517_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4521_ = v_a_4517_;
v_isShared_4522_ = v_isSharedCheck_4581_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_snd_4519_);
lean_inc(v_fst_4518_);
lean_dec(v_a_4517_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4581_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; uint8_t v___x_4527_; uint8_t v___x_4528_; lean_object* v___x_4529_; 
v___x_4523_ = lean_unsigned_to_nat(1u);
v___x_4524_ = lean_mk_empty_array_with_capacity(v___x_4523_);
v___x_4525_ = lean_array_push(v___x_4524_, v_b_4508_);
v___x_4526_ = 0;
v___x_4527_ = 1;
v___x_4528_ = 1;
lean_inc(v_fst_4518_);
v___x_4529_ = l_Lean_Meta_mkLambdaFVars(v___x_4525_, v_fst_4518_, v___x_4526_, v___x_4527_, v___x_4526_, v___x_4527_, v___x_4528_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4531_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
lean_inc(v_snd_4519_);
v___x_4531_ = l_Lean_Meta_mkLambdaFVars(v___x_4525_, v_snd_4519_, v___x_4526_, v___x_4527_, v___x_4526_, v___x_4527_, v___x_4528_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4533_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v___x_4533_ = l_Lean_Meta_mkForallFVars(v___x_4525_, v_fst_4518_, v___x_4526_, v___x_4527_, v___x_4527_, v___x_4528_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
lean_dec_ref(v___x_4525_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v___x_4533_, 1);
v___x_4535_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_4536_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_4535_, v_snd_4507_, v_a_4534_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4547_; 
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; 
v_unused_4548_ = lean_ctor_get(v___x_4536_, 0);
lean_dec(v_unused_4548_);
v___x_4538_ = v___x_4536_;
v_isShared_4539_ = v_isSharedCheck_4547_;
goto v_resetjp_4537_;
}
else
{
lean_dec(v___x_4536_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4547_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 0, v_a_4532_);
v___x_4541_ = v___x_4521_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4532_);
lean_ctor_set(v_reuseFailAlloc_4546_, 1, v_snd_4519_);
v___x_4541_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; lean_object* v___x_4544_; 
v___x_4542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4542_, 0, v_a_4530_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v___x_4542_);
v___x_4544_ = v___x_4538_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec(v_a_4532_);
lean_dec(v_a_4530_);
lean_del_object(v___x_4521_);
lean_dec(v_snd_4519_);
v_a_4549_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4536_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4536_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec(v_a_4532_);
lean_dec(v_a_4530_);
lean_del_object(v___x_4521_);
lean_dec(v_snd_4519_);
lean_dec_ref(v_snd_4507_);
v_a_4557_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4533_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4533_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
else
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
lean_dec(v_a_4530_);
lean_dec_ref(v___x_4525_);
lean_del_object(v___x_4521_);
lean_dec(v_snd_4519_);
lean_dec(v_fst_4518_);
lean_dec_ref(v_snd_4507_);
v_a_4565_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4531_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4531_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref(v___x_4525_);
lean_del_object(v___x_4521_);
lean_dec(v_snd_4519_);
lean_dec(v_fst_4518_);
lean_dec_ref(v_snd_4507_);
v_a_4573_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4529_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4529_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
lean_dec_ref(v_b_4508_);
lean_dec_ref(v_snd_4507_);
v_a_4582_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4516_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4516_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4587_; 
if (v_isShared_4585_ == 0)
{
v___x_4587_ = v___x_4584_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4588_; 
v_reuseFailAlloc_4588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4582_);
v___x_4587_ = v_reuseFailAlloc_4588_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
return v___x_4587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object* v_body_4590_, lean_object* v_snd_4591_, lean_object* v_b_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(v_body_4590_, v_snd_4591_, v_b_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec_ref(v_body_4590_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object* v_body_4599_, lean_object* v_snd_4600_, lean_object* v_name_4601_, uint8_t v_bi_4602_, lean_object* v_type_4603_, uint8_t v_kind_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
lean_object* v___f_4610_; lean_object* v___x_4611_; 
v___f_4610_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4610_, 0, v_body_4599_);
lean_closure_set(v___f_4610_, 1, v_snd_4600_);
v___x_4611_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4601_, v_bi_4602_, v_type_4603_, v___f_4610_, v_kind_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_a_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
v_a_4620_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4611_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4611_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object* v_body_4628_, lean_object* v_snd_4629_, lean_object* v_name_4630_, lean_object* v_bi_4631_, lean_object* v_type_4632_, lean_object* v_kind_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
uint8_t v_bi_boxed_4639_; uint8_t v_kind_boxed_4640_; lean_object* v_res_4641_; 
v_bi_boxed_4639_ = lean_unbox(v_bi_4631_);
v_kind_boxed_4640_ = lean_unbox(v_kind_4633_);
v_res_4641_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4628_, v_snd_4629_, v_name_4630_, v_bi_boxed_4639_, v_type_4632_, v_kind_boxed_4640_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
return v_res_4641_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0));
v___x_4644_ = l_Lean_stringToMessageData(v___x_4643_);
return v___x_4644_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6));
v___x_4653_ = l_Lean_stringToMessageData(v___x_4652_);
return v___x_4653_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8));
v___x_4656_ = l_Lean_stringToMessageData(v___x_4655_);
return v___x_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object* v_mvarId_4657_, lean_object* v_userName_x3f_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; uint8_t v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4688_; lean_object* v___y_4689_; lean_object* v___y_4693_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___x_4735_; 
lean_inc(v_mvarId_4657_);
v___x_4735_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_4657_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v_fst_4737_; lean_object* v_snd_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4871_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
lean_inc(v_a_4736_);
lean_dec_ref_known(v___x_4735_, 1);
v_fst_4737_ = lean_ctor_get(v_a_4736_, 0);
v_snd_4738_ = lean_ctor_get(v_a_4736_, 1);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_a_4736_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4740_ = v_a_4736_;
v_isShared_4741_ = v_isSharedCheck_4871_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_snd_4738_);
lean_inc(v_fst_4737_);
lean_dec(v_a_4736_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4871_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4742_; lean_object* v_a_4743_; lean_object* v___x_4744_; 
v___x_4742_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_4737_, v___y_4660_);
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc(v_a_4743_);
lean_dec_ref(v___x_4742_);
v___x_4744_ = l_Lean_Expr_cleanupAnnotations(v_a_4743_);
if (lean_obj_tag(v___x_4744_) == 7)
{
lean_object* v_binderName_4745_; lean_object* v_binderType_4746_; lean_object* v_body_4747_; uint8_t v_binderInfo_4748_; lean_object* v___x_4749_; 
lean_del_object(v___x_4740_);
v_binderName_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_binderName_4745_);
v_binderType_4746_ = lean_ctor_get(v___x_4744_, 1);
lean_inc_ref_n(v_binderType_4746_, 2);
v_body_4747_ = lean_ctor_get(v___x_4744_, 2);
lean_inc_ref(v_body_4747_);
v_binderInfo_4748_ = lean_ctor_get_uint8(v___x_4744_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_4744_, 3);
v___x_4749_ = l_Lean_Meta_getLevel(v_binderType_4746_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v_a_4750_; lean_object* v___x_4751_; lean_object* v_userName_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; 
v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
lean_inc(v_a_4750_);
lean_dec_ref_known(v___x_4749_, 1);
lean_inc_ref(v_body_4747_);
lean_inc_ref(v_binderType_4746_);
lean_inc(v_binderName_4745_);
v___x_4751_ = l_Lean_Expr_lam___override(v_binderName_4745_, v_binderType_4746_, v_body_4747_, v_binderInfo_4748_);
if (lean_obj_tag(v_userName_x3f_4658_) == 1)
{
lean_object* v_val_4794_; 
lean_dec(v_binderName_4745_);
v_val_4794_ = lean_ctor_get(v_userName_x3f_4658_, 0);
lean_inc(v_val_4794_);
lean_dec_ref_known(v_userName_x3f_4658_, 1);
v_userName_4753_ = v_val_4794_;
v___y_4754_ = v___y_4659_;
v___y_4755_ = v___y_4660_;
v___y_4756_ = v___y_4661_;
v___y_4757_ = v___y_4662_;
goto v___jp_4752_;
}
else
{
lean_object* v___x_4795_; 
lean_dec(v_userName_x3f_4658_);
v___x_4795_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_4745_, v___y_4659_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref_known(v___x_4795_, 1);
v_userName_4753_ = v_a_4796_;
v___y_4754_ = v___y_4659_;
v___y_4755_ = v___y_4660_;
v___y_4756_ = v___y_4661_;
v___y_4757_ = v___y_4662_;
goto v___jp_4752_;
}
else
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4804_; 
lean_dec_ref(v___x_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_body_4747_);
lean_dec_ref(v_binderType_4746_);
lean_dec(v_snd_4738_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_mvarId_4657_);
v_a_4797_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4804_ == 0)
{
v___x_4799_ = v___x_4795_;
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4795_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4804_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v___x_4802_; 
if (v_isShared_4800_ == 0)
{
v___x_4802_ = v___x_4799_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v_a_4797_);
v___x_4802_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
return v___x_4802_;
}
}
}
}
v___jp_4752_:
{
uint8_t v___x_4758_; lean_object* v___x_4759_; 
v___x_4758_ = 0;
lean_inc_ref(v_binderType_4746_);
v___x_4759_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4747_, v_snd_4738_, v_userName_4753_, v_binderInfo_4748_, v_binderType_4746_, v___x_4758_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec_ref(v___y_4754_);
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v_snd_4761_; lean_object* v_fst_4762_; lean_object* v_fst_4763_; lean_object* v_snd_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4785_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
lean_inc(v_a_4760_);
lean_dec_ref_known(v___x_4759_, 1);
v_snd_4761_ = lean_ctor_get(v_a_4760_, 1);
lean_inc(v_snd_4761_);
v_fst_4762_ = lean_ctor_get(v_a_4760_, 0);
lean_inc(v_fst_4762_);
lean_dec(v_a_4760_);
v_fst_4763_ = lean_ctor_get(v_snd_4761_, 0);
v_snd_4764_ = lean_ctor_get(v_snd_4761_, 1);
v_isSharedCheck_4785_ = !lean_is_exclusive(v_snd_4761_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4766_ = v_snd_4761_;
v_isShared_4767_ = v_isSharedCheck_4785_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_snd_4764_);
lean_inc(v_fst_4763_);
lean_dec(v_snd_4761_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4785_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4771_; 
v___x_4768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5));
v___x_4769_ = lean_box(0);
if (v_isShared_4767_ == 0)
{
lean_ctor_set_tag(v___x_4766_, 1);
lean_ctor_set(v___x_4766_, 1, v___x_4769_);
lean_ctor_set(v___x_4766_, 0, v_a_4750_);
v___x_4771_ = v___x_4766_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4750_);
lean_ctor_set(v_reuseFailAlloc_4784_, 1, v___x_4769_);
v___x_4771_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4782_; 
v___x_4772_ = l_Lean_mkConst(v___x_4768_, v___x_4771_);
v___x_4773_ = l_Lean_mkApp4(v___x_4772_, v_binderType_4746_, v___x_4751_, v_fst_4762_, v_fst_4763_);
v___x_4774_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4657_, v___x_4773_, v___y_4755_);
lean_dec(v___y_4755_);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4774_);
if (v_isSharedCheck_4782_ == 0)
{
lean_object* v_unused_4783_; 
v_unused_4783_ = lean_ctor_get(v___x_4774_, 0);
lean_dec(v_unused_4783_);
v___x_4776_ = v___x_4774_;
v_isShared_4777_ = v_isSharedCheck_4782_;
goto v_resetjp_4775_;
}
else
{
lean_dec(v___x_4774_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4782_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4778_; lean_object* v___x_4780_; 
v___x_4778_ = l_Lean_Expr_mvarId_x21(v_snd_4764_);
lean_dec(v_snd_4764_);
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 0, v___x_4778_);
v___x_4780_ = v___x_4776_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v___y_4755_);
lean_dec_ref(v___x_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_binderType_4746_);
lean_dec(v_mvarId_4657_);
v_a_4786_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4759_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4759_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_dec_ref(v_body_4747_);
lean_dec_ref(v_binderType_4746_);
lean_dec(v_binderName_4745_);
lean_dec(v_snd_4738_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v_a_4805_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4749_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4749_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
else
{
lean_object* v___x_4813_; 
lean_inc_ref(v___x_4744_);
lean_inc(v_mvarId_4657_);
v___x_4813_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4657_, v___x_4744_, v_snd_4738_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4862_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4816_ = v___x_4813_;
v_isShared_4817_ = v_isSharedCheck_4862_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4813_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4862_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
if (lean_obj_tag(v_a_4814_) == 1)
{
lean_object* v_val_4818_; lean_object* v___x_4820_; 
lean_dec_ref(v___x_4744_);
lean_del_object(v___x_4740_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v_val_4818_ = lean_ctor_get(v_a_4814_, 0);
lean_inc(v_val_4818_);
lean_dec_ref_known(v_a_4814_, 1);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v_val_4818_);
v___x_4820_ = v___x_4816_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_val_4818_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
else
{
lean_object* v___x_4822_; 
lean_del_object(v___x_4816_);
lean_dec(v_a_4814_);
lean_inc(v___y_4662_);
lean_inc_ref(v___y_4661_);
lean_inc(v___y_4660_);
lean_inc_ref(v___y_4659_);
lean_inc_ref(v___x_4744_);
v___x_4822_ = lean_infer_type(v___x_4744_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v___x_4824_ = l_Lean_Meta_whnfD(v_a_4823_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; uint8_t v___x_4826_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v___x_4824_, 1);
v___x_4826_ = l_Lean_Expr_isForall(v_a_4825_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4831_; 
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v___x_4827_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7);
v___x_4828_ = l_Lean_MessageData_ofExpr(v___x_4744_);
v___x_4829_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9);
if (v_isShared_4741_ == 0)
{
lean_ctor_set_tag(v___x_4740_, 7);
lean_ctor_set(v___x_4740_, 1, v___x_4829_);
lean_ctor_set(v___x_4740_, 0, v___x_4828_);
v___x_4831_ = v___x_4740_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4828_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
v___x_4832_ = l_Lean_MessageData_ofExpr(v_a_4825_);
v___x_4833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4831_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = l_Lean_indentD(v___x_4833_);
v___x_4835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4827_);
lean_ctor_set(v___x_4835_, 1, v___x_4834_);
v___x_4836_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4835_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
v_a_4837_ = lean_ctor_get(v___x_4836_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4836_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4836_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4836_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
else
{
lean_dec(v_a_4825_);
lean_dec_ref(v___x_4744_);
lean_del_object(v___x_4740_);
v___y_4693_ = v___y_4659_;
v___y_4694_ = v___y_4660_;
v___y_4695_ = v___y_4661_;
v___y_4696_ = v___y_4662_;
goto v___jp_4692_;
}
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_dec_ref(v___x_4744_);
lean_del_object(v___x_4740_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v_a_4846_ = lean_ctor_get(v___x_4824_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4824_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4824_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4824_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_dec_ref(v___x_4744_);
lean_del_object(v___x_4740_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v_a_4854_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4822_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4822_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_dec_ref(v___x_4744_);
lean_del_object(v___x_4740_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v_a_4863_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4813_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4813_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v_a_4872_ = lean_ctor_get(v___x_4735_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4735_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4735_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
v___jp_4664_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = lean_unsigned_to_nat(1u);
v___x_4673_ = l_Lean_Meta_introNCore(v___y_4665_, v___x_4672_, v___y_4671_, v___y_4669_, v___y_4669_, v___y_4668_, v___y_4666_, v___y_4670_, v___y_4667_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v_a_4674_; lean_object* v_snd_4675_; lean_object* v___x_4676_; 
v_a_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v___x_4673_, 1);
v_snd_4675_ = lean_ctor_get(v_a_4674_, 1);
lean_inc(v_snd_4675_);
lean_dec(v_a_4674_);
v___x_4676_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4675_, v___y_4668_, v___y_4666_, v___y_4670_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4668_);
return v___x_4676_;
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
lean_dec_ref(v___y_4670_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec(v___y_4666_);
v_a_4677_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v___x_4673_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4673_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
v___jp_4685_:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
v___x_4690_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1);
v___x_4691_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4690_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
return v___x_4691_;
}
v___jp_4692_:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3));
v___x_4698_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_4697_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; uint8_t v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4698_, 1);
v___x_4700_ = 0;
v___x_4701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2));
v___x_4702_ = lean_box(0);
v___x_4703_ = l_Lean_MVarId_apply(v_mvarId_4657_, v_a_4699_, v___x_4701_, v___x_4702_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
lean_inc(v_a_4704_);
lean_dec_ref_known(v___x_4703_, 1);
if (lean_obj_tag(v_a_4704_) == 1)
{
lean_object* v_tail_4705_; 
v_tail_4705_ = lean_ctor_get(v_a_4704_, 1);
if (lean_obj_tag(v_tail_4705_) == 0)
{
if (lean_obj_tag(v_userName_x3f_4658_) == 1)
{
lean_object* v_head_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4715_; 
v_head_4706_ = lean_ctor_get(v_a_4704_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_a_4704_);
if (v_isSharedCheck_4715_ == 0)
{
lean_object* v_unused_4716_; 
v_unused_4716_ = lean_ctor_get(v_a_4704_, 1);
lean_dec(v_unused_4716_);
v___x_4708_ = v_a_4704_;
v_isShared_4709_ = v_isSharedCheck_4715_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_head_4706_);
lean_dec(v_a_4704_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4715_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v_val_4710_; lean_object* v___x_4711_; lean_object* v___x_4713_; 
v_val_4710_ = lean_ctor_get(v_userName_x3f_4658_, 0);
lean_inc(v_val_4710_);
lean_dec_ref_known(v_userName_x3f_4658_, 1);
v___x_4711_ = lean_box(0);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 1, v___x_4711_);
lean_ctor_set(v___x_4708_, 0, v_val_4710_);
v___x_4713_ = v___x_4708_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_val_4710_);
lean_ctor_set(v_reuseFailAlloc_4714_, 1, v___x_4711_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
v___y_4665_ = v_head_4706_;
v___y_4666_ = v___y_4694_;
v___y_4667_ = v___y_4696_;
v___y_4668_ = v___y_4693_;
v___y_4669_ = v___x_4700_;
v___y_4670_ = v___y_4695_;
v___y_4671_ = v___x_4713_;
goto v___jp_4664_;
}
}
}
else
{
lean_object* v_head_4717_; lean_object* v___x_4718_; 
lean_dec(v_userName_x3f_4658_);
v_head_4717_ = lean_ctor_get(v_a_4704_, 0);
lean_inc(v_head_4717_);
lean_dec_ref_known(v_a_4704_, 2);
v___x_4718_ = lean_box(0);
v___y_4665_ = v_head_4717_;
v___y_4666_ = v___y_4694_;
v___y_4667_ = v___y_4696_;
v___y_4668_ = v___y_4693_;
v___y_4669_ = v___x_4700_;
v___y_4670_ = v___y_4695_;
v___y_4671_ = v___x_4718_;
goto v___jp_4664_;
}
}
else
{
lean_dec_ref_known(v_a_4704_, 2);
lean_dec(v_userName_x3f_4658_);
v___y_4686_ = v___y_4693_;
v___y_4687_ = v___y_4694_;
v___y_4688_ = v___y_4695_;
v___y_4689_ = v___y_4696_;
goto v___jp_4685_;
}
}
else
{
lean_dec(v_a_4704_);
lean_dec(v_userName_x3f_4658_);
v___y_4686_ = v___y_4693_;
v___y_4687_ = v___y_4694_;
v___y_4688_ = v___y_4695_;
v___y_4689_ = v___y_4696_;
goto v___jp_4685_;
}
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v_userName_x3f_4658_);
v_a_4719_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4703_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4703_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v_userName_x3f_4658_);
lean_dec(v_mvarId_4657_);
v_a_4727_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4698_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4698_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed(lean_object* v_mvarId_4880_, lean_object* v_userName_x3f_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(v_mvarId_4880_, v_userName_x3f_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(lean_object* v_mvarId_4888_, lean_object* v_userName_x3f_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v___f_4895_; lean_object* v___x_4896_; 
lean_inc(v_mvarId_4888_);
v___f_4895_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4895_, 0, v_mvarId_4888_);
lean_closure_set(v___f_4895_, 1, v_userName_x3f_4889_);
v___x_4896_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_4888_, v___f_4895_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___boxed(lean_object* v_mvarId_4897_, lean_object* v_userName_x3f_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_mvarId_4897_, v_userName_x3f_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
lean_dec(v_a_4902_);
lean_dec_ref(v_a_4901_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(lean_object* v_userName_x3f_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_){
_start:
{
lean_object* v___x_4912_; 
v___x_4912_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_a_4913_, v_userName_x3f_4905_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc(v_a_4915_);
lean_dec_ref_known(v___x_4914_, 1);
v___x_4916_ = lean_box(0);
v___x_4917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4917_, 0, v_a_4915_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
v___x_4918_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4917_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_);
return v___x_4918_;
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
v_a_4919_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4914_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4914_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
else
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
lean_dec(v_userName_x3f_4905_);
v_a_4927_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4912_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4912_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg___boxed(lean_object* v_userName_x3f_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_a_4936_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(lean_object* v_userName_x3f_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_){
_start:
{
lean_object* v___x_4953_; 
v___x_4953_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_4943_, v_a_4945_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___boxed(lean_object* v_userName_x3f_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(v_userName_x3f_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
return v_res_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(lean_object* v_as_4972_, size_t v_sz_4973_, size_t v_i_4974_, lean_object* v_b_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
uint8_t v___x_4982_; 
v___x_4982_ = lean_usize_dec_lt(v_i_4974_, v_sz_4973_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
v___x_4983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4983_, 0, v_b_4975_);
return v___x_4983_;
}
else
{
lean_object* v___x_4984_; lean_object* v_a_4985_; lean_object* v___y_4987_; lean_object* v___x_5010_; uint8_t v___x_5011_; 
v___x_4984_ = lean_box(0);
v_a_4985_ = lean_array_uget_borrowed(v_as_4972_, v_i_4974_);
v___x_5010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1));
lean_inc(v_a_4985_);
v___x_5011_ = l_Lean_Syntax_isOfKind(v_a_4985_, v___x_5010_);
if (v___x_5011_ == 0)
{
lean_object* v___x_5012_; 
v___x_5012_ = lean_box(0);
v___y_4987_ = v___x_5012_;
goto v___jp_4986_;
}
else
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; uint8_t v___x_5016_; 
v___x_5013_ = lean_unsigned_to_nat(0u);
v___x_5014_ = l_Lean_Syntax_getArg(v_a_4985_, v___x_5013_);
v___x_5015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3));
lean_inc(v___x_5014_);
v___x_5016_ = l_Lean_Syntax_isOfKind(v___x_5014_, v___x_5015_);
if (v___x_5016_ == 0)
{
lean_object* v___x_5017_; 
lean_dec(v___x_5014_);
v___x_5017_ = lean_box(0);
v___y_4987_ = v___x_5017_;
goto v___jp_4986_;
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5018_ = l_Lean_TSyntax_getId(v___x_5014_);
lean_dec(v___x_5014_);
v___x_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
v___y_4987_ = v___x_5019_;
goto v___jp_4986_;
}
}
v___jp_4986_:
{
lean_object* v_fileName_4988_; lean_object* v_fileMap_4989_; lean_object* v_options_4990_; lean_object* v_currRecDepth_4991_; lean_object* v_maxRecDepth_4992_; lean_object* v_ref_4993_; lean_object* v_currNamespace_4994_; lean_object* v_openDecls_4995_; lean_object* v_initHeartbeats_4996_; lean_object* v_maxHeartbeats_4997_; lean_object* v_quotContext_4998_; lean_object* v_currMacroScope_4999_; uint8_t v_diag_5000_; lean_object* v_cancelTk_x3f_5001_; uint8_t v_suppressElabErrors_5002_; lean_object* v_inheritedTraceOptions_5003_; lean_object* v_ref_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v_fileName_4988_ = lean_ctor_get(v___y_4979_, 0);
v_fileMap_4989_ = lean_ctor_get(v___y_4979_, 1);
v_options_4990_ = lean_ctor_get(v___y_4979_, 2);
v_currRecDepth_4991_ = lean_ctor_get(v___y_4979_, 3);
v_maxRecDepth_4992_ = lean_ctor_get(v___y_4979_, 4);
v_ref_4993_ = lean_ctor_get(v___y_4979_, 5);
v_currNamespace_4994_ = lean_ctor_get(v___y_4979_, 6);
v_openDecls_4995_ = lean_ctor_get(v___y_4979_, 7);
v_initHeartbeats_4996_ = lean_ctor_get(v___y_4979_, 8);
v_maxHeartbeats_4997_ = lean_ctor_get(v___y_4979_, 9);
v_quotContext_4998_ = lean_ctor_get(v___y_4979_, 10);
v_currMacroScope_4999_ = lean_ctor_get(v___y_4979_, 11);
v_diag_5000_ = lean_ctor_get_uint8(v___y_4979_, sizeof(void*)*14);
v_cancelTk_x3f_5001_ = lean_ctor_get(v___y_4979_, 12);
v_suppressElabErrors_5002_ = lean_ctor_get_uint8(v___y_4979_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5003_ = lean_ctor_get(v___y_4979_, 13);
v_ref_5004_ = l_Lean_replaceRef(v_a_4985_, v_ref_4993_);
lean_inc_ref(v_inheritedTraceOptions_5003_);
lean_inc(v_cancelTk_x3f_5001_);
lean_inc(v_currMacroScope_4999_);
lean_inc(v_quotContext_4998_);
lean_inc(v_maxHeartbeats_4997_);
lean_inc(v_initHeartbeats_4996_);
lean_inc(v_openDecls_4995_);
lean_inc(v_currNamespace_4994_);
lean_inc(v_maxRecDepth_4992_);
lean_inc(v_currRecDepth_4991_);
lean_inc_ref(v_options_4990_);
lean_inc_ref(v_fileMap_4989_);
lean_inc_ref(v_fileName_4988_);
v___x_5005_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5005_, 0, v_fileName_4988_);
lean_ctor_set(v___x_5005_, 1, v_fileMap_4989_);
lean_ctor_set(v___x_5005_, 2, v_options_4990_);
lean_ctor_set(v___x_5005_, 3, v_currRecDepth_4991_);
lean_ctor_set(v___x_5005_, 4, v_maxRecDepth_4992_);
lean_ctor_set(v___x_5005_, 5, v_ref_5004_);
lean_ctor_set(v___x_5005_, 6, v_currNamespace_4994_);
lean_ctor_set(v___x_5005_, 7, v_openDecls_4995_);
lean_ctor_set(v___x_5005_, 8, v_initHeartbeats_4996_);
lean_ctor_set(v___x_5005_, 9, v_maxHeartbeats_4997_);
lean_ctor_set(v___x_5005_, 10, v_quotContext_4998_);
lean_ctor_set(v___x_5005_, 11, v_currMacroScope_4999_);
lean_ctor_set(v___x_5005_, 12, v_cancelTk_x3f_5001_);
lean_ctor_set(v___x_5005_, 13, v_inheritedTraceOptions_5003_);
lean_ctor_set_uint8(v___x_5005_, sizeof(void*)*14, v_diag_5000_);
lean_ctor_set_uint8(v___x_5005_, sizeof(void*)*14 + 1, v_suppressElabErrors_5002_);
v___x_5006_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___y_4987_, v___y_4976_, v___y_4977_, v___y_4978_, v___x_5005_, v___y_4980_);
lean_dec_ref_known(v___x_5005_, 14);
if (lean_obj_tag(v___x_5006_) == 0)
{
size_t v___x_5007_; size_t v___x_5008_; 
lean_dec_ref_known(v___x_5006_, 1);
v___x_5007_ = ((size_t)1ULL);
v___x_5008_ = lean_usize_add(v_i_4974_, v___x_5007_);
v_i_4974_ = v___x_5008_;
v_b_4975_ = v___x_4984_;
goto _start;
}
else
{
return v___x_5006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object* v_as_5020_, lean_object* v_sz_5021_, lean_object* v_i_5022_, lean_object* v_b_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
size_t v_sz_boxed_5030_; size_t v_i_boxed_5031_; lean_object* v_res_5032_; 
v_sz_boxed_5030_ = lean_unbox_usize(v_sz_5021_);
lean_dec(v_sz_5021_);
v_i_boxed_5031_ = lean_unbox_usize(v_i_5022_);
lean_dec(v_i_5022_);
v_res_5032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5020_, v_sz_boxed_5030_, v_i_boxed_5031_, v_b_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v_as_5020_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object* v_stx_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_){
_start:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v_ids_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; 
v___x_5043_ = lean_unsigned_to_nat(1u);
v___x_5044_ = l_Lean_Syntax_getArg(v_stx_5033_, v___x_5043_);
v_ids_5045_ = l_Lean_Syntax_getArgs(v___x_5044_);
lean_dec(v___x_5044_);
v___x_5046_ = lean_array_get_size(v_ids_5045_);
v___x_5047_ = lean_unsigned_to_nat(0u);
v___x_5048_ = lean_nat_dec_eq(v___x_5046_, v___x_5047_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5049_; size_t v_sz_5050_; size_t v___x_5051_; lean_object* v___x_5052_; 
v___x_5049_ = lean_box(0);
v_sz_5050_ = lean_array_size(v_ids_5045_);
v___x_5051_ = ((size_t)0ULL);
v___x_5052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_ids_5045_, v_sz_5050_, v___x_5051_, v___x_5049_, v_a_5035_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
lean_dec_ref(v_ids_5045_);
if (lean_obj_tag(v___x_5052_) == 0)
{
lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5059_ == 0)
{
lean_object* v_unused_5060_; 
v_unused_5060_ = lean_ctor_get(v___x_5052_, 0);
lean_dec(v_unused_5060_);
v___x_5054_ = v___x_5052_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_dec(v___x_5052_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5049_);
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5049_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
else
{
return v___x_5052_;
}
}
else
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
lean_dec_ref(v_ids_5045_);
v___x_5061_ = lean_box(0);
v___x_5062_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___x_5061_, v_a_5035_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_);
return v___x_5062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object* v_stx_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Lean_Elab_Tactic_Conv_evalExt(v_stx_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
lean_dec(v_a_5071_);
lean_dec_ref(v_a_5070_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
lean_dec(v_stx_5063_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object* v_as_5074_, size_t v_sz_5075_, size_t v_i_5076_, lean_object* v_b_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v___x_5087_; 
v___x_5087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5074_, v_sz_5075_, v_i_5076_, v_b_5077_, v___y_5079_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object* v_as_5088_, lean_object* v_sz_5089_, lean_object* v_i_5090_, lean_object* v_b_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
size_t v_sz_boxed_5101_; size_t v_i_boxed_5102_; lean_object* v_res_5103_; 
v_sz_boxed_5101_ = lean_unbox_usize(v_sz_5089_);
lean_dec(v_sz_5089_);
v_i_boxed_5102_ = lean_unbox_usize(v_i_5090_);
lean_dec(v_i_5090_);
v_res_5103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(v_as_5088_, v_sz_boxed_5101_, v_i_boxed_5102_, v_b_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_, v___y_5099_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec_ref(v_as_5088_);
return v_res_5103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1(){
_start:
{
lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; 
v___x_5118_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5119_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0));
v___x_5120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5121_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExt___boxed), 10, 0);
v___x_5122_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5118_, v___x_5119_, v___x_5120_, v___x_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3(){
_start:
{
lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; 
v___x_5151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6));
v___x_5153_ = l_Lean_addBuiltinDeclarationRanges(v___x_5151_, v___x_5152_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object* v_a_5154_){
_start:
{
lean_object* v_res_5155_; 
v_res_5155_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object* v_a_5156_, lean_object* v_trees_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
lean_object* v___x_5167_; 
lean_inc(v___y_5165_);
lean_inc_ref(v___y_5164_);
lean_inc(v___y_5163_);
lean_inc_ref(v___y_5162_);
lean_inc(v___y_5161_);
lean_inc_ref(v___y_5160_);
lean_inc(v___y_5159_);
lean_inc_ref(v___y_5158_);
v___x_5167_ = lean_apply_9(v_a_5156_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, lean_box(0));
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5176_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5170_ = v___x_5167_;
v_isShared_5171_ = v_isSharedCheck_5176_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5167_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5176_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5172_; lean_object* v___x_5174_; 
v___x_5172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5172_, 0, v_a_5168_);
lean_ctor_set(v___x_5172_, 1, v_trees_5157_);
if (v_isShared_5171_ == 0)
{
lean_ctor_set(v___x_5170_, 0, v___x_5172_);
v___x_5174_ = v___x_5170_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v___x_5172_);
v___x_5174_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
return v___x_5174_;
}
}
}
else
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5184_; 
lean_dec_ref(v_trees_5157_);
v_a_5177_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5179_ = v___x_5167_;
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5167_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5182_; 
if (v_isShared_5180_ == 0)
{
v___x_5182_ = v___x_5179_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object* v_a_5185_, lean_object* v_trees_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_){
_start:
{
lean_object* v_res_5196_; 
v_res_5196_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(v_a_5185_, v_trees_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_);
lean_dec(v___y_5194_);
lean_dec_ref(v___y_5193_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
return v_res_5196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object* v___x_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_){
_start:
{
lean_object* v___x_5207_; 
v___x_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5197_);
return v___x_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object* v___x_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v_res_5218_; 
v_res_5218_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(v___x_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(lean_object* v_a_5219_, lean_object* v_trees_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v___x_5230_; 
lean_inc(v___y_5228_);
lean_inc_ref(v___y_5227_);
lean_inc(v___y_5226_);
lean_inc_ref(v___y_5225_);
lean_inc(v___y_5224_);
lean_inc_ref(v___y_5223_);
lean_inc(v___y_5222_);
lean_inc_ref(v___y_5221_);
v___x_5230_ = lean_apply_9(v_a_5219_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, lean_box(0));
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5239_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5239_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5239_ == 0)
{
v___x_5233_ = v___x_5230_;
v_isShared_5234_ = v_isSharedCheck_5239_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5230_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5239_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5235_; lean_object* v___x_5237_; 
v___x_5235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5235_, 0, v_a_5231_);
lean_ctor_set(v___x_5235_, 1, v_trees_5220_);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v___x_5235_);
v___x_5237_ = v___x_5233_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5238_; 
v_reuseFailAlloc_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5238_, 0, v___x_5235_);
v___x_5237_ = v_reuseFailAlloc_5238_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
return v___x_5237_;
}
}
}
else
{
lean_object* v_a_5240_; lean_object* v___x_5242_; uint8_t v_isShared_5243_; uint8_t v_isSharedCheck_5247_; 
lean_dec_ref(v_trees_5220_);
v_a_5240_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5247_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5247_ == 0)
{
v___x_5242_ = v___x_5230_;
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
else
{
lean_inc(v_a_5240_);
lean_dec(v___x_5230_);
v___x_5242_ = lean_box(0);
v_isShared_5243_ = v_isSharedCheck_5247_;
goto v_resetjp_5241_;
}
v_resetjp_5241_:
{
lean_object* v___x_5245_; 
if (v_isShared_5243_ == 0)
{
v___x_5245_ = v___x_5242_;
goto v_reusejp_5244_;
}
else
{
lean_object* v_reuseFailAlloc_5246_; 
v_reuseFailAlloc_5246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5246_, 0, v_a_5240_);
v___x_5245_ = v_reuseFailAlloc_5246_;
goto v_reusejp_5244_;
}
v_reusejp_5244_:
{
return v___x_5245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object* v_a_5248_, lean_object* v_trees_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v_res_5259_; 
v_res_5259_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(v_a_5248_, v_trees_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
return v_res_5259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(uint8_t v___x_5260_, lean_object* v___x_5261_, lean_object* v___x_5262_, lean_object* v___x_5263_, lean_object* v___x_5264_, lean_object* v___x_5265_, lean_object* v___x_5266_, lean_object* v___x_5267_, lean_object* v___x_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_){
_start:
{
if (v___x_5260_ == 0)
{
lean_object* v___x_5278_; 
lean_dec_ref(v___y_5275_);
lean_dec(v___x_5268_);
lean_dec_ref(v___x_5267_);
lean_dec_ref(v___x_5266_);
lean_dec_ref(v___x_5265_);
lean_dec_ref(v___x_5264_);
v___x_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5261_);
return v___x_5278_;
}
else
{
lean_object* v_fileName_5279_; lean_object* v_fileMap_5280_; lean_object* v_options_5281_; lean_object* v_currRecDepth_5282_; lean_object* v_maxRecDepth_5283_; lean_object* v_ref_5284_; lean_object* v_currNamespace_5285_; lean_object* v_openDecls_5286_; lean_object* v_initHeartbeats_5287_; lean_object* v_maxHeartbeats_5288_; lean_object* v_quotContext_5289_; lean_object* v_currMacroScope_5290_; uint8_t v_diag_5291_; lean_object* v_cancelTk_x3f_5292_; uint8_t v_suppressElabErrors_5293_; lean_object* v_inheritedTraceOptions_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5324_; 
v_fileName_5279_ = lean_ctor_get(v___y_5275_, 0);
v_fileMap_5280_ = lean_ctor_get(v___y_5275_, 1);
v_options_5281_ = lean_ctor_get(v___y_5275_, 2);
v_currRecDepth_5282_ = lean_ctor_get(v___y_5275_, 3);
v_maxRecDepth_5283_ = lean_ctor_get(v___y_5275_, 4);
v_ref_5284_ = lean_ctor_get(v___y_5275_, 5);
v_currNamespace_5285_ = lean_ctor_get(v___y_5275_, 6);
v_openDecls_5286_ = lean_ctor_get(v___y_5275_, 7);
v_initHeartbeats_5287_ = lean_ctor_get(v___y_5275_, 8);
v_maxHeartbeats_5288_ = lean_ctor_get(v___y_5275_, 9);
v_quotContext_5289_ = lean_ctor_get(v___y_5275_, 10);
v_currMacroScope_5290_ = lean_ctor_get(v___y_5275_, 11);
v_diag_5291_ = lean_ctor_get_uint8(v___y_5275_, sizeof(void*)*14);
v_cancelTk_x3f_5292_ = lean_ctor_get(v___y_5275_, 12);
v_suppressElabErrors_5293_ = lean_ctor_get_uint8(v___y_5275_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5294_ = lean_ctor_get(v___y_5275_, 13);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___y_5275_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5296_ = v___y_5275_;
v_isShared_5297_ = v_isSharedCheck_5324_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_inheritedTraceOptions_5294_);
lean_inc(v_cancelTk_x3f_5292_);
lean_inc(v_currMacroScope_5290_);
lean_inc(v_quotContext_5289_);
lean_inc(v_maxHeartbeats_5288_);
lean_inc(v_initHeartbeats_5287_);
lean_inc(v_openDecls_5286_);
lean_inc(v_currNamespace_5285_);
lean_inc(v_ref_5284_);
lean_inc(v_maxRecDepth_5283_);
lean_inc(v_currRecDepth_5282_);
lean_inc(v_options_5281_);
lean_inc(v_fileMap_5280_);
lean_inc(v_fileName_5279_);
lean_dec(v___y_5275_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5324_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v_ref_5298_; lean_object* v___x_5300_; 
v_ref_5298_ = l_Lean_replaceRef(v___x_5262_, v_ref_5284_);
lean_dec(v_ref_5284_);
lean_inc(v_ref_5298_);
if (v_isShared_5297_ == 0)
{
lean_ctor_set(v___x_5296_, 5, v_ref_5298_);
v___x_5300_ = v___x_5296_;
goto v_reusejp_5299_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_fileName_5279_);
lean_ctor_set(v_reuseFailAlloc_5323_, 1, v_fileMap_5280_);
lean_ctor_set(v_reuseFailAlloc_5323_, 2, v_options_5281_);
lean_ctor_set(v_reuseFailAlloc_5323_, 3, v_currRecDepth_5282_);
lean_ctor_set(v_reuseFailAlloc_5323_, 4, v_maxRecDepth_5283_);
lean_ctor_set(v_reuseFailAlloc_5323_, 5, v_ref_5298_);
lean_ctor_set(v_reuseFailAlloc_5323_, 6, v_currNamespace_5285_);
lean_ctor_set(v_reuseFailAlloc_5323_, 7, v_openDecls_5286_);
lean_ctor_set(v_reuseFailAlloc_5323_, 8, v_initHeartbeats_5287_);
lean_ctor_set(v_reuseFailAlloc_5323_, 9, v_maxHeartbeats_5288_);
lean_ctor_set(v_reuseFailAlloc_5323_, 10, v_quotContext_5289_);
lean_ctor_set(v_reuseFailAlloc_5323_, 11, v_currMacroScope_5290_);
lean_ctor_set(v_reuseFailAlloc_5323_, 12, v_cancelTk_x3f_5292_);
lean_ctor_set(v_reuseFailAlloc_5323_, 13, v_inheritedTraceOptions_5294_);
lean_ctor_set_uint8(v_reuseFailAlloc_5323_, sizeof(void*)*14, v_diag_5291_);
lean_ctor_set_uint8(v_reuseFailAlloc_5323_, sizeof(void*)*14 + 1, v_suppressElabErrors_5293_);
v___x_5300_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5299_;
}
v_reusejp_5299_:
{
lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; uint8_t v___x_5304_; 
v___x_5301_ = l_Lean_Syntax_getArg(v___x_5262_, v___x_5263_);
v___x_5302_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__4));
lean_inc_ref(v___x_5267_);
lean_inc_ref(v___x_5266_);
lean_inc_ref(v___x_5265_);
lean_inc_ref(v___x_5264_);
v___x_5303_ = l_Lean_Name_mkStr5(v___x_5264_, v___x_5265_, v___x_5266_, v___x_5267_, v___x_5302_);
lean_inc(v___x_5301_);
v___x_5304_ = l_Lean_Syntax_isOfKind(v___x_5301_, v___x_5303_);
lean_dec(v___x_5303_);
if (v___x_5304_ == 0)
{
lean_object* v___x_5305_; lean_object* v___x_5306_; uint8_t v___x_5307_; 
v___x_5305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0));
lean_inc_ref(v___x_5264_);
v___x_5306_ = l_Lean_Name_mkStr2(v___x_5264_, v___x_5305_);
lean_inc(v___x_5301_);
v___x_5307_ = l_Lean_Syntax_isOfKind(v___x_5301_, v___x_5306_);
lean_dec(v___x_5306_);
if (v___x_5307_ == 0)
{
lean_object* v___x_5308_; 
lean_dec(v___x_5301_);
lean_dec_ref(v___x_5300_);
lean_dec(v_ref_5298_);
lean_dec(v___x_5268_);
lean_dec_ref(v___x_5267_);
lean_dec_ref(v___x_5266_);
lean_dec_ref(v___x_5265_);
lean_dec_ref(v___x_5264_);
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5261_);
return v___x_5308_;
}
else
{
lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5309_ = l_Lean_SourceInfo_fromRef(v_ref_5298_, v___x_5304_);
lean_dec(v_ref_5298_);
v___x_5310_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_5311_ = l_Lean_Name_mkStr5(v___x_5264_, v___x_5265_, v___x_5266_, v___x_5267_, v___x_5310_);
lean_inc_n(v___x_5309_, 2);
v___x_5312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5312_, 0, v___x_5309_);
lean_ctor_set(v___x_5312_, 1, v___x_5310_);
v___x_5313_ = l_Lean_Syntax_node1(v___x_5309_, v___x_5268_, v___x_5301_);
v___x_5314_ = l_Lean_Syntax_node2(v___x_5309_, v___x_5311_, v___x_5312_, v___x_5313_);
v___x_5315_ = l_Lean_Elab_Tactic_evalTactic(v___x_5314_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___x_5300_, v___y_5276_);
lean_dec_ref(v___x_5300_);
return v___x_5315_;
}
}
else
{
uint8_t v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
lean_dec(v___x_5268_);
v___x_5316_ = 0;
v___x_5317_ = l_Lean_SourceInfo_fromRef(v_ref_5298_, v___x_5316_);
lean_dec(v_ref_5298_);
v___x_5318_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_5319_ = l_Lean_Name_mkStr5(v___x_5264_, v___x_5265_, v___x_5266_, v___x_5267_, v___x_5318_);
lean_inc(v___x_5317_);
v___x_5320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5320_, 0, v___x_5317_);
lean_ctor_set(v___x_5320_, 1, v___x_5318_);
v___x_5321_ = l_Lean_Syntax_node2(v___x_5317_, v___x_5319_, v___x_5320_, v___x_5301_);
v___x_5322_ = l_Lean_Elab_Tactic_evalTactic(v___x_5321_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___x_5300_, v___y_5276_);
lean_dec_ref(v___x_5300_);
return v___x_5322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5325_ = _args[0];
lean_object* v___x_5326_ = _args[1];
lean_object* v___x_5327_ = _args[2];
lean_object* v___x_5328_ = _args[3];
lean_object* v___x_5329_ = _args[4];
lean_object* v___x_5330_ = _args[5];
lean_object* v___x_5331_ = _args[6];
lean_object* v___x_5332_ = _args[7];
lean_object* v___x_5333_ = _args[8];
lean_object* v___y_5334_ = _args[9];
lean_object* v___y_5335_ = _args[10];
lean_object* v___y_5336_ = _args[11];
lean_object* v___y_5337_ = _args[12];
lean_object* v___y_5338_ = _args[13];
lean_object* v___y_5339_ = _args[14];
lean_object* v___y_5340_ = _args[15];
lean_object* v___y_5341_ = _args[16];
lean_object* v___y_5342_ = _args[17];
_start:
{
uint8_t v___x_16237__boxed_5343_; lean_object* v_res_5344_; 
v___x_16237__boxed_5343_ = lean_unbox(v___x_5325_);
v_res_5344_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(v___x_16237__boxed_5343_, v___x_5326_, v___x_5327_, v___x_5328_, v___x_5329_, v___x_5330_, v___x_5331_, v___x_5332_, v___x_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
lean_dec(v___y_5341_);
lean_dec(v___y_5339_);
lean_dec_ref(v___y_5338_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___x_5328_);
lean_dec(v___x_5327_);
return v_res_5344_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5345_ = lean_unsigned_to_nat(32u);
v___x_5346_ = lean_mk_empty_array_with_capacity(v___x_5345_);
v___x_5347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5347_, 0, v___x_5346_);
return v___x_5347_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5348_ = ((size_t)5ULL);
v___x_5349_ = lean_unsigned_to_nat(0u);
v___x_5350_ = lean_unsigned_to_nat(32u);
v___x_5351_ = lean_mk_empty_array_with_capacity(v___x_5350_);
v___x_5352_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0);
v___x_5353_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5353_, 0, v___x_5352_);
lean_ctor_set(v___x_5353_, 1, v___x_5351_);
lean_ctor_set(v___x_5353_, 2, v___x_5349_);
lean_ctor_set(v___x_5353_, 3, v___x_5349_);
lean_ctor_set_usize(v___x_5353_, 4, v___x_5348_);
return v___x_5353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object* v___y_5354_){
_start:
{
lean_object* v___x_5356_; lean_object* v_infoState_5357_; lean_object* v_trees_5358_; lean_object* v___x_5359_; lean_object* v_infoState_5360_; lean_object* v_env_5361_; lean_object* v_nextMacroScope_5362_; lean_object* v_ngen_5363_; lean_object* v_auxDeclNGen_5364_; lean_object* v_traceState_5365_; lean_object* v_cache_5366_; lean_object* v_messages_5367_; lean_object* v_snapshotTasks_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5389_; 
v___x_5356_ = lean_st_ref_get(v___y_5354_);
v_infoState_5357_ = lean_ctor_get(v___x_5356_, 7);
lean_inc_ref(v_infoState_5357_);
lean_dec(v___x_5356_);
v_trees_5358_ = lean_ctor_get(v_infoState_5357_, 2);
lean_inc_ref(v_trees_5358_);
lean_dec_ref(v_infoState_5357_);
v___x_5359_ = lean_st_ref_take(v___y_5354_);
v_infoState_5360_ = lean_ctor_get(v___x_5359_, 7);
v_env_5361_ = lean_ctor_get(v___x_5359_, 0);
v_nextMacroScope_5362_ = lean_ctor_get(v___x_5359_, 1);
v_ngen_5363_ = lean_ctor_get(v___x_5359_, 2);
v_auxDeclNGen_5364_ = lean_ctor_get(v___x_5359_, 3);
v_traceState_5365_ = lean_ctor_get(v___x_5359_, 4);
v_cache_5366_ = lean_ctor_get(v___x_5359_, 5);
v_messages_5367_ = lean_ctor_get(v___x_5359_, 6);
v_snapshotTasks_5368_ = lean_ctor_get(v___x_5359_, 8);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5370_ = v___x_5359_;
v_isShared_5371_ = v_isSharedCheck_5389_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_snapshotTasks_5368_);
lean_inc(v_infoState_5360_);
lean_inc(v_messages_5367_);
lean_inc(v_cache_5366_);
lean_inc(v_traceState_5365_);
lean_inc(v_auxDeclNGen_5364_);
lean_inc(v_ngen_5363_);
lean_inc(v_nextMacroScope_5362_);
lean_inc(v_env_5361_);
lean_dec(v___x_5359_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5389_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
uint8_t v_enabled_5372_; lean_object* v_assignment_5373_; lean_object* v_lazyAssignment_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5387_; 
v_enabled_5372_ = lean_ctor_get_uint8(v_infoState_5360_, sizeof(void*)*3);
v_assignment_5373_ = lean_ctor_get(v_infoState_5360_, 0);
v_lazyAssignment_5374_ = lean_ctor_get(v_infoState_5360_, 1);
v_isSharedCheck_5387_ = !lean_is_exclusive(v_infoState_5360_);
if (v_isSharedCheck_5387_ == 0)
{
lean_object* v_unused_5388_; 
v_unused_5388_ = lean_ctor_get(v_infoState_5360_, 2);
lean_dec(v_unused_5388_);
v___x_5376_ = v_infoState_5360_;
v_isShared_5377_ = v_isSharedCheck_5387_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_lazyAssignment_5374_);
lean_inc(v_assignment_5373_);
lean_dec(v_infoState_5360_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5387_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5378_; lean_object* v___x_5380_; 
v___x_5378_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1);
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 2, v___x_5378_);
v___x_5380_ = v___x_5376_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5386_; 
v_reuseFailAlloc_5386_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_assignment_5373_);
lean_ctor_set(v_reuseFailAlloc_5386_, 1, v_lazyAssignment_5374_);
lean_ctor_set(v_reuseFailAlloc_5386_, 2, v___x_5378_);
lean_ctor_set_uint8(v_reuseFailAlloc_5386_, sizeof(void*)*3, v_enabled_5372_);
v___x_5380_ = v_reuseFailAlloc_5386_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
lean_object* v___x_5382_; 
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 7, v___x_5380_);
v___x_5382_ = v___x_5370_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_env_5361_);
lean_ctor_set(v_reuseFailAlloc_5385_, 1, v_nextMacroScope_5362_);
lean_ctor_set(v_reuseFailAlloc_5385_, 2, v_ngen_5363_);
lean_ctor_set(v_reuseFailAlloc_5385_, 3, v_auxDeclNGen_5364_);
lean_ctor_set(v_reuseFailAlloc_5385_, 4, v_traceState_5365_);
lean_ctor_set(v_reuseFailAlloc_5385_, 5, v_cache_5366_);
lean_ctor_set(v_reuseFailAlloc_5385_, 6, v_messages_5367_);
lean_ctor_set(v_reuseFailAlloc_5385_, 7, v___x_5380_);
lean_ctor_set(v_reuseFailAlloc_5385_, 8, v_snapshotTasks_5368_);
v___x_5382_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5383_ = lean_st_ref_put(v___y_5354_, v___x_5382_);
v___x_5384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5384_, 0, v_trees_5358_);
return v___x_5384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v_res_5392_; 
v_res_5392_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5390_);
lean_dec(v___y_5390_);
return v_res_5392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object* v___y_5393_, lean_object* v_mkInfoTree_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v_a_5402_, lean_object* v_a_x3f_5403_){
_start:
{
lean_object* v___x_5405_; lean_object* v_infoState_5406_; lean_object* v_trees_5407_; lean_object* v___x_5408_; 
v___x_5405_ = lean_st_ref_get(v___y_5393_);
v_infoState_5406_ = lean_ctor_get(v___x_5405_, 7);
lean_inc_ref(v_infoState_5406_);
lean_dec(v___x_5405_);
v_trees_5407_ = lean_ctor_get(v_infoState_5406_, 2);
lean_inc_ref(v_trees_5407_);
lean_dec_ref(v_infoState_5406_);
lean_inc(v___y_5393_);
lean_inc_ref(v___y_5401_);
lean_inc(v___y_5400_);
lean_inc_ref(v___y_5399_);
lean_inc(v___y_5398_);
lean_inc_ref(v___y_5397_);
lean_inc(v___y_5396_);
lean_inc_ref(v___y_5395_);
v___x_5408_ = lean_apply_10(v_mkInfoTree_5394_, v_trees_5407_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5393_, lean_box(0));
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v_a_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5447_; 
v_a_5409_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5411_ = v___x_5408_;
v_isShared_5412_ = v_isSharedCheck_5447_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_a_5409_);
lean_dec(v___x_5408_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5447_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v___x_5413_; lean_object* v_infoState_5414_; lean_object* v_env_5415_; lean_object* v_nextMacroScope_5416_; lean_object* v_ngen_5417_; lean_object* v_auxDeclNGen_5418_; lean_object* v_traceState_5419_; lean_object* v_cache_5420_; lean_object* v_messages_5421_; lean_object* v_snapshotTasks_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5446_; 
v___x_5413_ = lean_st_ref_take(v___y_5393_);
v_infoState_5414_ = lean_ctor_get(v___x_5413_, 7);
v_env_5415_ = lean_ctor_get(v___x_5413_, 0);
v_nextMacroScope_5416_ = lean_ctor_get(v___x_5413_, 1);
v_ngen_5417_ = lean_ctor_get(v___x_5413_, 2);
v_auxDeclNGen_5418_ = lean_ctor_get(v___x_5413_, 3);
v_traceState_5419_ = lean_ctor_get(v___x_5413_, 4);
v_cache_5420_ = lean_ctor_get(v___x_5413_, 5);
v_messages_5421_ = lean_ctor_get(v___x_5413_, 6);
v_snapshotTasks_5422_ = lean_ctor_get(v___x_5413_, 8);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5424_ = v___x_5413_;
v_isShared_5425_ = v_isSharedCheck_5446_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_snapshotTasks_5422_);
lean_inc(v_infoState_5414_);
lean_inc(v_messages_5421_);
lean_inc(v_cache_5420_);
lean_inc(v_traceState_5419_);
lean_inc(v_auxDeclNGen_5418_);
lean_inc(v_ngen_5417_);
lean_inc(v_nextMacroScope_5416_);
lean_inc(v_env_5415_);
lean_dec(v___x_5413_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5446_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
uint8_t v_enabled_5426_; lean_object* v_assignment_5427_; lean_object* v_lazyAssignment_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5444_; 
v_enabled_5426_ = lean_ctor_get_uint8(v_infoState_5414_, sizeof(void*)*3);
v_assignment_5427_ = lean_ctor_get(v_infoState_5414_, 0);
v_lazyAssignment_5428_ = lean_ctor_get(v_infoState_5414_, 1);
v_isSharedCheck_5444_ = !lean_is_exclusive(v_infoState_5414_);
if (v_isSharedCheck_5444_ == 0)
{
lean_object* v_unused_5445_; 
v_unused_5445_ = lean_ctor_get(v_infoState_5414_, 2);
lean_dec(v_unused_5445_);
v___x_5430_ = v_infoState_5414_;
v_isShared_5431_ = v_isSharedCheck_5444_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_lazyAssignment_5428_);
lean_inc(v_assignment_5427_);
lean_dec(v_infoState_5414_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5444_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5432_; lean_object* v___x_5434_; 
v___x_5432_ = l_Lean_PersistentArray_push___redArg(v_a_5402_, v_a_5409_);
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 2, v___x_5432_);
v___x_5434_ = v___x_5430_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_assignment_5427_);
lean_ctor_set(v_reuseFailAlloc_5443_, 1, v_lazyAssignment_5428_);
lean_ctor_set(v_reuseFailAlloc_5443_, 2, v___x_5432_);
lean_ctor_set_uint8(v_reuseFailAlloc_5443_, sizeof(void*)*3, v_enabled_5426_);
v___x_5434_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5436_; 
if (v_isShared_5425_ == 0)
{
lean_ctor_set(v___x_5424_, 7, v___x_5434_);
v___x_5436_ = v___x_5424_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_env_5415_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v_nextMacroScope_5416_);
lean_ctor_set(v_reuseFailAlloc_5442_, 2, v_ngen_5417_);
lean_ctor_set(v_reuseFailAlloc_5442_, 3, v_auxDeclNGen_5418_);
lean_ctor_set(v_reuseFailAlloc_5442_, 4, v_traceState_5419_);
lean_ctor_set(v_reuseFailAlloc_5442_, 5, v_cache_5420_);
lean_ctor_set(v_reuseFailAlloc_5442_, 6, v_messages_5421_);
lean_ctor_set(v_reuseFailAlloc_5442_, 7, v___x_5434_);
lean_ctor_set(v_reuseFailAlloc_5442_, 8, v_snapshotTasks_5422_);
v___x_5436_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5440_; 
v___x_5437_ = lean_st_ref_put(v___y_5393_, v___x_5436_);
v___x_5438_ = lean_box(0);
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 0, v___x_5438_);
v___x_5440_ = v___x_5411_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5438_);
v___x_5440_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
return v___x_5440_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5455_; 
lean_dec_ref(v_a_5402_);
v_a_5448_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5450_ = v___x_5408_;
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_dec(v___x_5408_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v___x_5453_; 
if (v_isShared_5451_ == 0)
{
v___x_5453_ = v___x_5450_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_a_5448_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
return v___x_5453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object* v___y_5456_, lean_object* v_mkInfoTree_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v_a_5465_, lean_object* v_a_x3f_5466_, lean_object* v___y_5467_){
_start:
{
lean_object* v_res_5468_; 
v_res_5468_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5456_, v_mkInfoTree_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v_a_5465_, v_a_x3f_5466_);
lean_dec(v_a_x3f_5466_);
lean_dec_ref(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5456_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object* v_x_5469_, lean_object* v_mkInfoTree_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_){
_start:
{
lean_object* v___x_5480_; lean_object* v_infoState_5481_; uint8_t v_enabled_5482_; 
v___x_5480_ = lean_st_ref_get(v___y_5478_);
v_infoState_5481_ = lean_ctor_get(v___x_5480_, 7);
lean_inc_ref(v_infoState_5481_);
lean_dec(v___x_5480_);
v_enabled_5482_ = lean_ctor_get_uint8(v_infoState_5481_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5481_);
if (v_enabled_5482_ == 0)
{
lean_object* v___x_5483_; 
lean_dec_ref(v_mkInfoTree_5470_);
lean_inc(v___y_5478_);
lean_inc_ref(v___y_5477_);
lean_inc(v___y_5476_);
lean_inc_ref(v___y_5475_);
lean_inc(v___y_5474_);
lean_inc_ref(v___y_5473_);
lean_inc(v___y_5472_);
lean_inc_ref(v___y_5471_);
v___x_5483_ = lean_apply_9(v_x_5469_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, lean_box(0));
return v___x_5483_;
}
else
{
lean_object* v___x_5484_; lean_object* v_a_5485_; lean_object* v_r_5486_; 
v___x_5484_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5478_);
v_a_5485_ = lean_ctor_get(v___x_5484_, 0);
lean_inc(v_a_5485_);
lean_dec_ref(v___x_5484_);
lean_inc(v___y_5478_);
lean_inc_ref(v___y_5477_);
lean_inc(v___y_5476_);
lean_inc_ref(v___y_5475_);
lean_inc(v___y_5474_);
lean_inc_ref(v___y_5473_);
lean_inc(v___y_5472_);
lean_inc_ref(v___y_5471_);
v_r_5486_ = lean_apply_9(v_x_5469_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, lean_box(0));
if (lean_obj_tag(v_r_5486_) == 0)
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5511_; 
v_a_5487_ = lean_ctor_get(v_r_5486_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v_r_5486_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5489_ = v_r_5486_;
v_isShared_5490_ = v_isSharedCheck_5511_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v_r_5486_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5511_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
lean_inc(v_a_5487_);
if (v_isShared_5490_ == 0)
{
lean_ctor_set_tag(v___x_5489_, 1);
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5493_; 
v___x_5493_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5478_, v_mkInfoTree_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v_a_5485_, v___x_5492_);
lean_dec_ref(v___x_5492_);
if (lean_obj_tag(v___x_5493_) == 0)
{
lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5500_; 
v_isSharedCheck_5500_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5500_ == 0)
{
lean_object* v_unused_5501_; 
v_unused_5501_ = lean_ctor_get(v___x_5493_, 0);
lean_dec(v_unused_5501_);
v___x_5495_ = v___x_5493_;
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
else
{
lean_dec(v___x_5493_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5500_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5498_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v_a_5487_);
v___x_5498_ = v___x_5495_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5487_);
v___x_5498_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
return v___x_5498_;
}
}
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_a_5487_);
v_a_5502_ = lean_ctor_get(v___x_5493_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5493_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5493_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
}
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; 
v_a_5512_ = lean_ctor_get(v_r_5486_, 0);
lean_inc(v_a_5512_);
lean_dec_ref_known(v_r_5486_, 1);
v___x_5513_ = lean_box(0);
v___x_5514_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5478_, v_mkInfoTree_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v_a_5485_, v___x_5513_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5521_; 
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; 
v_unused_5522_ = lean_ctor_get(v___x_5514_, 0);
lean_dec(v_unused_5522_);
v___x_5516_ = v___x_5514_;
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
else
{
lean_dec(v___x_5514_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5519_; 
if (v_isShared_5517_ == 0)
{
lean_ctor_set_tag(v___x_5516_, 1);
lean_ctor_set(v___x_5516_, 0, v_a_5512_);
v___x_5519_ = v___x_5516_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5512_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
else
{
lean_object* v_a_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
lean_dec(v_a_5512_);
v_a_5523_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5525_ = v___x_5514_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_a_5523_);
lean_dec(v___x_5514_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
return v___x_5528_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object* v_x_5531_, lean_object* v_mkInfoTree_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_){
_start:
{
lean_object* v_res_5542_; 
v_res_5542_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5531_, v_mkInfoTree_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec(v___y_5534_);
lean_dec_ref(v___y_5533_);
return v_res_5542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object* v_upperBound_5553_, lean_object* v_enterArgsAndSeps_5554_, lean_object* v_a_5555_, lean_object* v_b_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_){
_start:
{
uint8_t v___x_5566_; 
v___x_5566_ = lean_nat_dec_lt(v_a_5555_, v_upperBound_5553_);
if (v___x_5566_ == 0)
{
lean_object* v___x_5567_; 
lean_dec(v_a_5555_);
v___x_5567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5567_, 0, v_b_5556_);
return v___x_5567_;
}
else
{
lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___y_5576_; lean_object* v___x_5605_; lean_object* v___x_5606_; uint8_t v___x_5607_; 
v___x_5568_ = lean_unsigned_to_nat(2u);
v___x_5569_ = lean_box(0);
v___x_5570_ = lean_box(0);
v___x_5571_ = lean_unsigned_to_nat(0u);
v___x_5572_ = lean_unsigned_to_nat(1u);
v___x_5573_ = lean_nat_mul(v___x_5568_, v_a_5555_);
v___x_5574_ = lean_array_get_borrowed(v___x_5569_, v_enterArgsAndSeps_5554_, v___x_5573_);
v___x_5605_ = lean_nat_add(v___x_5573_, v___x_5572_);
lean_dec(v___x_5573_);
v___x_5606_ = lean_array_get_size(v_enterArgsAndSeps_5554_);
v___x_5607_ = lean_nat_dec_lt(v___x_5605_, v___x_5606_);
if (v___x_5607_ == 0)
{
lean_dec(v___x_5605_);
v___y_5576_ = v___x_5569_;
goto v___jp_5575_;
}
else
{
lean_object* v___x_5608_; 
v___x_5608_ = lean_array_fget_borrowed(v_enterArgsAndSeps_5554_, v___x_5605_);
lean_dec(v___x_5605_);
lean_inc(v___x_5608_);
v___y_5576_ = v___x_5608_;
goto v___jp_5575_;
}
v___jp_5575_:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; 
v___x_5577_ = lean_mk_empty_array_with_capacity(v___x_5568_);
lean_inc(v___x_5574_);
v___x_5578_ = lean_array_push(v___x_5577_, v___x_5574_);
v___x_5579_ = lean_array_push(v___x_5578_, v___y_5576_);
v___x_5580_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5581_ = lean_box(2);
v___x_5582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
lean_ctor_set(v___x_5582_, 1, v___x_5580_);
lean_ctor_set(v___x_5582_, 2, v___x_5579_);
v___x_5583_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5582_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
if (lean_obj_tag(v___x_5583_) == 0)
{
lean_object* v_a_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; uint8_t v___x_5590_; lean_object* v___x_5591_; lean_object* v___f_5592_; lean_object* v___f_5593_; lean_object* v___x_5594_; 
v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
lean_inc(v_a_5584_);
lean_dec_ref_known(v___x_5583_, 1);
v___x_5585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0));
v___x_5586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1));
v___x_5587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2));
v___x_5588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3));
v___x_5589_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3));
lean_inc_n(v___x_5574_, 2);
v___x_5590_ = l_Lean_Syntax_isOfKind(v___x_5574_, v___x_5589_);
v___x_5591_ = lean_box(v___x_5590_);
v___f_5592_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_5592_, 0, v___x_5591_);
lean_closure_set(v___f_5592_, 1, v___x_5570_);
lean_closure_set(v___f_5592_, 2, v___x_5574_);
lean_closure_set(v___f_5592_, 3, v___x_5571_);
lean_closure_set(v___f_5592_, 4, v___x_5585_);
lean_closure_set(v___f_5592_, 5, v___x_5586_);
lean_closure_set(v___f_5592_, 6, v___x_5587_);
lean_closure_set(v___f_5592_, 7, v___x_5588_);
lean_closure_set(v___f_5592_, 8, v___x_5580_);
v___f_5593_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5593_, 0, v_a_5584_);
v___x_5594_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5592_, v___f_5593_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v___x_5595_; 
lean_dec_ref_known(v___x_5594_, 1);
v___x_5595_ = lean_nat_add(v_a_5555_, v___x_5572_);
lean_dec(v_a_5555_);
v_a_5555_ = v___x_5595_;
v_b_5556_ = v___x_5570_;
goto _start;
}
else
{
lean_dec(v_a_5555_);
return v___x_5594_;
}
}
else
{
lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5604_; 
lean_dec(v_a_5555_);
v_a_5597_ = lean_ctor_get(v___x_5583_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5583_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5599_ = v___x_5583_;
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_dec(v___x_5583_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5602_; 
if (v_isShared_5600_ == 0)
{
v___x_5602_ = v___x_5599_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object* v_upperBound_5609_, lean_object* v_enterArgsAndSeps_5610_, lean_object* v_a_5611_, lean_object* v_b_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5609_, v_enterArgsAndSeps_5610_, v_a_5611_, v_b_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
lean_dec(v___y_5620_);
lean_dec_ref(v___y_5619_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec(v___y_5616_);
lean_dec_ref(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v___y_5613_);
lean_dec_ref(v_enterArgsAndSeps_5610_);
lean_dec(v_upperBound_5609_);
return v_res_5622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object* v_stx_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_){
_start:
{
lean_object* v___x_5635_; lean_object* v_token_5636_; lean_object* v___x_5637_; lean_object* v_lbrak_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5646_; 
v___x_5635_ = lean_unsigned_to_nat(0u);
v_token_5636_ = l_Lean_Syntax_getArg(v_stx_5625_, v___x_5635_);
v___x_5637_ = lean_unsigned_to_nat(1u);
v_lbrak_5638_ = l_Lean_Syntax_getArg(v_stx_5625_, v___x_5637_);
v___x_5639_ = lean_unsigned_to_nat(2u);
v___x_5640_ = lean_mk_empty_array_with_capacity(v___x_5639_);
v___x_5641_ = lean_array_push(v___x_5640_, v_token_5636_);
v___x_5642_ = lean_array_push(v___x_5641_, v_lbrak_5638_);
v___x_5643_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5644_ = lean_box(2);
v___x_5645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set(v___x_5645_, 1, v___x_5643_);
lean_ctor_set(v___x_5645_, 2, v___x_5642_);
v___x_5646_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5645_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; lean_object* v___f_5648_; lean_object* v___x_5649_; lean_object* v___f_5650_; lean_object* v___x_5651_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
lean_inc(v_a_5647_);
lean_dec_ref_known(v___x_5646_, 1);
v___f_5648_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5648_, 0, v_a_5647_);
v___x_5649_ = lean_box(0);
v___f_5650_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalEnter___closed__0));
v___x_5651_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5650_, v___f_5648_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v___x_5652_; lean_object* v_enterArgsAndSeps_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; 
lean_dec_ref_known(v___x_5651_, 1);
v___x_5652_ = l_Lean_Syntax_getArg(v_stx_5625_, v___x_5639_);
v_enterArgsAndSeps_5653_ = l_Lean_Syntax_getArgs(v___x_5652_);
lean_dec(v___x_5652_);
v___x_5654_ = lean_array_get_size(v_enterArgsAndSeps_5653_);
v___x_5655_ = lean_nat_add(v___x_5654_, v___x_5637_);
v___x_5656_ = lean_nat_shiftr(v___x_5655_, v___x_5637_);
lean_dec(v___x_5655_);
v___x_5657_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v___x_5656_, v_enterArgsAndSeps_5653_, v___x_5635_, v___x_5649_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_);
lean_dec_ref(v_enterArgsAndSeps_5653_);
lean_dec(v___x_5656_);
if (lean_obj_tag(v___x_5657_) == 0)
{
lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5664_; 
v_isSharedCheck_5664_ = !lean_is_exclusive(v___x_5657_);
if (v_isSharedCheck_5664_ == 0)
{
lean_object* v_unused_5665_; 
v_unused_5665_ = lean_ctor_get(v___x_5657_, 0);
lean_dec(v_unused_5665_);
v___x_5659_ = v___x_5657_;
v_isShared_5660_ = v_isSharedCheck_5664_;
goto v_resetjp_5658_;
}
else
{
lean_dec(v___x_5657_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5664_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5662_; 
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v___x_5649_);
v___x_5662_ = v___x_5659_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v___x_5649_);
v___x_5662_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
return v___x_5662_;
}
}
}
else
{
return v___x_5657_;
}
}
else
{
return v___x_5651_;
}
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
v_a_5666_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5646_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5646_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object* v_stx_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_){
_start:
{
lean_object* v_res_5684_; 
v_res_5684_ = l_Lean_Elab_Tactic_Conv_evalEnter(v_stx_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_);
lean_dec(v_a_5682_);
lean_dec_ref(v_a_5681_);
lean_dec(v_a_5680_);
lean_dec_ref(v_a_5679_);
lean_dec(v_a_5678_);
lean_dec_ref(v_a_5677_);
lean_dec(v_a_5676_);
lean_dec_ref(v_a_5675_);
lean_dec(v_stx_5674_);
return v_res_5684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v___x_5694_; 
v___x_5694_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5692_);
return v___x_5694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_){
_start:
{
lean_object* v_res_5704_; 
v_res_5704_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_, v___y_5702_);
lean_dec(v___y_5702_);
lean_dec_ref(v___y_5701_);
lean_dec(v___y_5700_);
lean_dec_ref(v___y_5699_);
lean_dec(v___y_5698_);
lean_dec_ref(v___y_5697_);
lean_dec(v___y_5696_);
lean_dec_ref(v___y_5695_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object* v_00_u03b1_5705_, lean_object* v_x_5706_, lean_object* v_mkInfoTree_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5706_, v_mkInfoTree_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object* v_00_u03b1_5718_, lean_object* v_x_5719_, lean_object* v_mkInfoTree_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
lean_object* v_res_5730_; 
v_res_5730_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(v_00_u03b1_5718_, v_x_5719_, v_mkInfoTree_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_);
lean_dec(v___y_5728_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
return v_res_5730_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object* v_upperBound_5731_, lean_object* v_enterArgsAndSeps_5732_, lean_object* v_inst_5733_, lean_object* v_R_5734_, lean_object* v_a_5735_, lean_object* v_b_5736_, lean_object* v_c_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v___x_5747_; 
v___x_5747_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5731_, v_enterArgsAndSeps_5732_, v_a_5735_, v_b_5736_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object* v_upperBound_5748_, lean_object* v_enterArgsAndSeps_5749_, lean_object* v_inst_5750_, lean_object* v_R_5751_, lean_object* v_a_5752_, lean_object* v_b_5753_, lean_object* v_c_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(v_upperBound_5748_, v_enterArgsAndSeps_5749_, v_inst_5750_, v_R_5751_, v_a_5752_, v_b_5753_, v_c_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec_ref(v_enterArgsAndSeps_5749_);
lean_dec(v_upperBound_5748_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1(){
_start:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; 
v___x_5780_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1));
v___x_5782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3));
v___x_5783_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___boxed), 10, 0);
v___x_5784_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5780_, v___x_5781_, v___x_5782_, v___x_5783_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object* v_a_5785_){
_start:
{
lean_object* v_res_5786_; 
v_res_5786_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
return v_res_5786_;
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
