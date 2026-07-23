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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_dec(v_tail_163_);
lean_dec_ref_known(v_tail_162_, 2);
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
v___x_684_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_633_, v_fst_671_, v___x_683_, v_addImplicitArgs_636_, v_nameSubgoals_637_, v___y_677_, v___y_678_, v___y_676_, v___y_679_);
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
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_682_, v_fst_672_, v___y_677_, v___y_678_, v___y_676_, v___y_679_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_mkEqTrans(v_a_691_, v_fst_687_, v___y_677_, v___y_678_, v___y_676_, v___y_679_);
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
v___y_676_ = v___y_715_;
v___y_677_ = v___y_713_;
v___y_678_ = v___y_714_;
v___y_679_ = v___y_716_;
v_lower_680_ = v___x_717_;
v_upper_681_ = v___x_650_;
goto v___jp_675_;
}
else
{
lean_dec(v___x_717_);
v___y_676_ = v___y_715_;
v___y_677_ = v___y_713_;
v___y_678_ = v___y_714_;
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
v___x_971_ = lean_st_ref_set(v___y_952_, v___x_970_);
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
size_t v_x_3120__boxed_1199_; size_t v_x_3121__boxed_1200_; lean_object* v_res_1201_; 
v_x_3120__boxed_1199_ = lean_unbox_usize(v_x_1195_);
lean_dec(v_x_1195_);
v_x_3121__boxed_1200_ = lean_unbox_usize(v_x_1196_);
lean_dec(v_x_1196_);
v_res_1201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1194_, v_x_3120__boxed_1199_, v_x_3121__boxed_1200_, v_x_1197_, v_x_1198_);
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
lean_object* v___x_1213_; lean_object* v_mctx_1214_; lean_object* v_cache_1215_; lean_object* v_zetaDeltaFVarIds_1216_; lean_object* v_postponed_1217_; lean_object* v_diag_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1246_; 
v___x_1213_ = lean_st_ref_take(v___y_1211_);
v_mctx_1214_ = lean_ctor_get(v___x_1213_, 0);
v_cache_1215_ = lean_ctor_get(v___x_1213_, 1);
v_zetaDeltaFVarIds_1216_ = lean_ctor_get(v___x_1213_, 2);
v_postponed_1217_ = lean_ctor_get(v___x_1213_, 3);
v_diag_1218_ = lean_ctor_get(v___x_1213_, 4);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1220_ = v___x_1213_;
v_isShared_1221_ = v_isSharedCheck_1246_;
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
v_isShared_1221_ = v_isSharedCheck_1246_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_depth_1222_; lean_object* v_levelAssignDepth_1223_; lean_object* v_lmvarCounter_1224_; lean_object* v_mvarCounter_1225_; lean_object* v_lDecls_1226_; lean_object* v_decls_1227_; lean_object* v_userNames_1228_; lean_object* v_lAssignment_1229_; lean_object* v_eAssignment_1230_; lean_object* v_dAssignment_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1245_; 
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
v_isSharedCheck_1245_ = !lean_is_exclusive(v_mctx_1214_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1233_ = v_mctx_1214_;
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
else
{
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
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1245_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_1230_, v_mvarId_1209_, v_val_1210_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 8, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_depth_1222_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_levelAssignDepth_1223_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_lmvarCounter_1224_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_mvarCounter_1225_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_lDecls_1226_);
lean_ctor_set(v_reuseFailAlloc_1244_, 5, v_decls_1227_);
lean_ctor_set(v_reuseFailAlloc_1244_, 6, v_userNames_1228_);
lean_ctor_set(v_reuseFailAlloc_1244_, 7, v_lAssignment_1229_);
lean_ctor_set(v_reuseFailAlloc_1244_, 8, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1244_, 9, v_dAssignment_1231_);
v___x_1237_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1237_);
v___x_1239_ = v___x_1220_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_cache_1215_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_zetaDeltaFVarIds_1216_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_postponed_1217_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_diag_1218_);
v___x_1239_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_st_ref_set(v___y_1211_, v___x_1239_);
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
size_t v_x_3618__boxed_1443_; size_t v_x_3619__boxed_1444_; lean_object* v_res_1445_; 
v_x_3618__boxed_1443_ = lean_unbox_usize(v_x_1439_);
lean_dec(v_x_1439_);
v_x_3619__boxed_1444_ = lean_unbox_usize(v_x_1440_);
lean_dec(v_x_1440_);
v_res_1445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(v_00_u03b2_1437_, v_x_1438_, v_x_3618__boxed_1443_, v_x_3619__boxed_1444_, v_x_1441_, v_x_1442_);
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
v___y_2081_ = v___y_2119_;
v___y_2082_ = v_snd_2132_;
v___y_2083_ = v___y_2120_;
v___y_2084_ = v___y_2117_;
v___y_2085_ = v_fst_2130_;
v___y_2086_ = v_fst_2131_;
v___y_2087_ = v___y_2118_;
v_lower_2088_ = v___x_2121_;
v_upper_2089_ = v___x_2105_;
goto v___jp_2080_;
}
else
{
v___y_2081_ = v___y_2119_;
v___y_2082_ = v_snd_2132_;
v___y_2083_ = v___y_2120_;
v___y_2084_ = v___y_2117_;
v___y_2085_ = v_fst_2130_;
v___y_2086_ = v_fst_2131_;
v___y_2087_ = v___y_2118_;
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
lean_ctor_set(v___x_2077_, 1, v___y_2075_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___y_2074_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
v___jp_2080_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = l_Array_toSubarray___redArg(v_args_2067_, v_lower_2088_, v_upper_2089_);
v___x_2091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_2090_, v___y_2085_, v___y_2084_, v___y_2087_, v___y_2081_, v___y_2083_);
if (lean_obj_tag(v___x_2091_) == 0)
{
if (lean_obj_tag(v___y_2086_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3);
v___x_2094_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(v___x_2093_);
v___y_2074_ = v_a_2092_;
v___y_2075_ = v___y_2082_;
v___y_2076_ = v___x_2094_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2095_; lean_object* v_val_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2091_, 1);
v_val_2096_ = lean_ctor_get(v___y_2086_, 0);
lean_inc(v_val_2096_);
lean_dec_ref_known(v___y_2086_, 1);
v___y_2074_ = v_a_2095_;
v___y_2075_ = v___y_2082_;
v___y_2076_ = v_val_2096_;
goto v___jp_2073_;
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v___y_2086_);
lean_dec(v___y_2082_);
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
lean_object* v___f_2239_; lean_object* v___x_4889__overap_2240_; lean_object* v___x_2241_; 
v___f_2239_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_4889__overap_2240_ = lean_panic_fn_borrowed(v___f_2239_, v_msg_2233_);
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
v___x_2241_ = lean_apply_5(v___x_4889__overap_2240_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, lean_box(0));
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
uint8_t v_domain_boxed_2387_; uint8_t v___x_5312__boxed_2388_; lean_object* v_res_2389_; 
v_domain_boxed_2387_ = lean_unbox(v_domain_2376_);
v___x_5312__boxed_2388_ = lean_unbox(v___x_2377_);
v_res_2389_ = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(v_binderType_2373_, v_mvarId_2374_, v_body_2375_, v_domain_boxed_2387_, v___x_5312__boxed_2388_, v_binderName_2378_, v_tacticName_2379_, v_rhs_2380_, v_arg_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
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
lean_object* v_snd_2826_; lean_object* v_fst_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; uint8_t v___x_2830_; 
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
v___x_2830_ = l_Lean_Expr_isForall(v_fst_2827_);
if (v___x_2830_ == 0)
{
lean_object* v_keyedConfig_2831_; uint8_t v_trackZetaDelta_2832_; lean_object* v_zetaDeltaSet_2833_; lean_object* v_lctx_2834_; lean_object* v_localInstances_2835_; lean_object* v_defEqCtx_x3f_2836_; lean_object* v_synthPendingDepth_2837_; lean_object* v_customCanUnfoldPredicate_x3f_2838_; uint8_t v_univApprox_2839_; uint8_t v_inTypeClassResolution_2840_; uint8_t v_cacheInferType_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v_keyedConfig_2831_ = lean_ctor_get(v___y_2796_, 0);
v_trackZetaDelta_2832_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7);
v_zetaDeltaSet_2833_ = lean_ctor_get(v___y_2796_, 1);
v_lctx_2834_ = lean_ctor_get(v___y_2796_, 2);
v_localInstances_2835_ = lean_ctor_get(v___y_2796_, 3);
v_defEqCtx_x3f_2836_ = lean_ctor_get(v___y_2796_, 4);
v_synthPendingDepth_2837_ = lean_ctor_get(v___y_2796_, 5);
v_customCanUnfoldPredicate_x3f_2838_ = lean_ctor_get(v___y_2796_, 6);
v_univApprox_2839_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2840_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7 + 2);
v_cacheInferType_2841_ = lean_ctor_get_uint8(v___y_2796_, sizeof(void*)*7 + 3);
v___x_2842_ = 0;
v___x_2843_ = lean_expr_instantiate_rev_range(v_fst_2827_, v_fst_2828_, v_a_2794_, v_xs_2793_);
lean_dec(v_fst_2828_);
lean_dec(v_fst_2827_);
lean_inc_ref(v_keyedConfig_2831_);
v___x_2844_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2842_, v_keyedConfig_2831_);
lean_inc(v_customCanUnfoldPredicate_x3f_2838_);
lean_inc(v_synthPendingDepth_2837_);
lean_inc(v_defEqCtx_x3f_2836_);
lean_inc_ref(v_localInstances_2835_);
lean_inc_ref(v_lctx_2834_);
lean_inc(v_zetaDeltaSet_2833_);
v___x_2845_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v_zetaDeltaSet_2833_);
lean_ctor_set(v___x_2845_, 2, v_lctx_2834_);
lean_ctor_set(v___x_2845_, 3, v_localInstances_2835_);
lean_ctor_set(v___x_2845_, 4, v_defEqCtx_x3f_2836_);
lean_ctor_set(v___x_2845_, 5, v_synthPendingDepth_2837_);
lean_ctor_set(v___x_2845_, 6, v_customCanUnfoldPredicate_x3f_2838_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7, v_trackZetaDelta_2832_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7 + 1, v_univApprox_2839_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2840_);
lean_ctor_set_uint8(v___x_2845_, sizeof(void*)*7 + 3, v_cacheInferType_2841_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
v___x_2846_ = lean_whnf(v___x_2843_, v___x_2845_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = lean_box(0);
lean_inc(v_a_2794_);
v___x_2849_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2829_, v_a_2794_, v___x_2848_, v_a_2847_, v_a_2794_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
v___y_2802_ = v___x_2849_;
goto v___jp_2801_;
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_snd_2829_);
lean_dec(v_a_2794_);
v_a_2850_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2846_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2846_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_box(0);
lean_inc(v_a_2794_);
v___x_2859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2829_, v_a_2794_, v___x_2858_, v_fst_2827_, v_fst_2828_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v_fst_2828_);
v___y_2802_ = v___x_2859_;
goto v___jp_2801_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object* v_upperBound_2860_, lean_object* v_xs_2861_, lean_object* v_a_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_2860_, v_xs_2861_, v_a_2862_, v_b_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_xs_2861_);
lean_dec(v_upperBound_2860_);
return v_res_2869_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2));
v___x_2877_ = l_Lean_stringToMessageData(v___x_2876_);
return v___x_2877_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4));
v___x_2880_ = l_Lean_stringToMessageData(v___x_2879_);
return v___x_2880_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_unsigned_to_nat(0u);
v___x_2882_ = lean_nat_to_int(v___x_2881_);
return v___x_2882_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = lean_nat_to_int(v___x_2883_);
return v___x_2884_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8));
v___x_2887_ = l_Lean_stringToMessageData(v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object* v_tacticName_2888_, uint8_t v_explicit_2889_, lean_object* v_f_2890_, lean_object* v_xs_2891_, lean_object* v_i_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___y_2899_; lean_object* v_lower_2900_; lean_object* v_upper_2901_; lean_object* v___y_2907_; lean_object* v_lower_2908_; lean_object* v_upper_2909_; 
if (v_explicit_2889_ == 0)
{
lean_object* v___x_2914_; 
lean_inc(v_a_2896_);
lean_inc_ref(v_a_2895_);
lean_inc(v_a_2894_);
lean_inc_ref(v_a_2893_);
lean_inc_ref(v_f_2890_);
v___x_2914_ = lean_infer_type(v_f_2890_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = lean_array_get_size(v_xs_2891_);
v___x_2917_ = lean_unsigned_to_nat(0u);
v___x_2918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1));
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v_a_2915_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v___x_2916_, v_xs_2891_, v___x_2917_, v___x_2919_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v_snd_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2980_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v_snd_2922_ = lean_ctor_get(v_a_2921_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_a_2921_);
if (v_isSharedCheck_2980_ == 0)
{
lean_object* v_unused_2981_; 
v_unused_2981_ = lean_ctor_get(v_a_2921_, 0);
lean_dec(v_unused_2981_);
v___x_2924_ = v_a_2921_;
v_isShared_2925_ = v_isSharedCheck_2980_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_snd_2922_);
lean_dec(v_a_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2980_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v_snd_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2978_; 
v_snd_2926_ = lean_ctor_get(v_snd_2922_, 1);
v_isSharedCheck_2978_ = !lean_is_exclusive(v_snd_2922_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v_snd_2922_, 0);
lean_dec(v_unused_2979_);
v___x_2928_ = v_snd_2922_;
v_isShared_2929_ = v_isSharedCheck_2978_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_snd_2926_);
lean_dec(v_snd_2922_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2978_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___y_2931_; lean_object* v___y_2939_; lean_object* v___x_2965_; lean_object* v___y_2967_; uint8_t v___x_2972_; 
v___x_2965_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_2972_ = lean_int_dec_lt(v___x_2965_, v_i_2892_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_array_get_size(v_snd_2926_);
v___x_2974_ = lean_nat_to_int(v___x_2973_);
v___x_2975_ = lean_int_add(v_i_2892_, v___x_2974_);
lean_dec(v___x_2974_);
v___y_2967_ = v___x_2975_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_2977_ = lean_int_sub(v_i_2892_, v___x_2976_);
v___y_2967_ = v___x_2977_;
goto v___jp_2966_;
}
v___jp_2930_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2932_ = lean_nat_abs(v___y_2931_);
lean_dec(v___y_2931_);
v___x_2933_ = lean_array_get(v___x_2917_, v_snd_2926_, v___x_2932_);
lean_dec(v___x_2932_);
lean_dec(v_snd_2926_);
lean_inc(v___x_2933_);
lean_inc_ref(v_xs_2891_);
v___x_2934_ = l_Array_toSubarray___redArg(v_xs_2891_, v___x_2917_, v___x_2933_);
v___x_2935_ = l_Subarray_copy___redArg(v___x_2934_);
v___x_2936_ = l_Lean_mkAppN(v_f_2890_, v___x_2935_);
lean_dec_ref(v___x_2935_);
v___x_2937_ = lean_nat_dec_le(v___x_2933_, v___x_2917_);
if (v___x_2937_ == 0)
{
v___y_2907_ = v___x_2936_;
v_lower_2908_ = v___x_2933_;
v_upper_2909_ = v___x_2916_;
goto v___jp_2906_;
}
else
{
lean_dec(v___x_2933_);
v___y_2907_ = v___x_2936_;
v_lower_2908_ = v___x_2917_;
v_upper_2909_ = v___x_2916_;
goto v___jp_2906_;
}
}
v___jp_2938_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
lean_dec(v___y_2939_);
v___x_2940_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_2941_ = l_Lean_stringToMessageData(v_tacticName_2888_);
if (v_isShared_2929_ == 0)
{
lean_ctor_set_tag(v___x_2928_, 7);
lean_ctor_set(v___x_2928_, 1, v___x_2941_);
lean_ctor_set(v___x_2928_, 0, v___x_2940_);
v___x_2943_ = v___x_2928_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 7);
lean_ctor_set(v___x_2924_, 1, v___x_2944_);
lean_ctor_set(v___x_2924_, 0, v___x_2943_);
v___x_2946_ = v___x_2924_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
v___x_2947_ = lean_array_get_size(v_snd_2926_);
lean_dec(v_snd_2926_);
v___x_2948_ = l_Nat_reprFast(v___x_2947_);
v___x_2949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
v___x_2950_ = l_Lean_MessageData_ofFormat(v___x_2949_);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2946_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2951_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2953_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
v___jp_2966_:
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_int_dec_lt(v___y_2967_, v___x_2965_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2969_ = lean_array_get_size(v_snd_2926_);
v___x_2970_ = lean_nat_to_int(v___x_2969_);
v___x_2971_ = lean_int_dec_le(v___x_2970_, v___y_2967_);
lean_dec(v___x_2970_);
if (v___x_2971_ == 0)
{
lean_del_object(v___x_2928_);
lean_del_object(v___x_2924_);
lean_dec_ref(v_tacticName_2888_);
v___y_2931_ = v___y_2967_;
goto v___jp_2930_;
}
else
{
lean_dec_ref(v_xs_2891_);
lean_dec_ref(v_f_2890_);
v___y_2939_ = v___y_2967_;
goto v___jp_2938_;
}
}
else
{
lean_dec_ref(v_xs_2891_);
lean_dec_ref(v_f_2890_);
v___y_2939_ = v___y_2967_;
goto v___jp_2938_;
}
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref(v_xs_2891_);
lean_dec_ref(v_f_2890_);
lean_dec_ref(v_tacticName_2888_);
v_a_2982_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2920_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2920_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref(v_xs_2891_);
lean_dec_ref(v_f_2890_);
lean_dec_ref(v_tacticName_2888_);
v_a_2990_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2914_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2914_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v___x_2998_; lean_object* v___y_3000_; lean_object* v___y_3008_; lean_object* v___x_3030_; lean_object* v___y_3032_; uint8_t v___x_3037_; 
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3037_ = lean_int_dec_lt(v___x_3030_, v_i_2892_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = lean_array_get_size(v_xs_2891_);
v___x_3039_ = lean_nat_to_int(v___x_3038_);
v___x_3040_ = lean_int_add(v_i_2892_, v___x_3039_);
lean_dec(v___x_3039_);
v___y_3032_ = v___x_3040_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3042_ = lean_int_sub(v_i_2892_, v___x_3041_);
v___y_3032_ = v___x_3042_;
goto v___jp_3031_;
}
v___jp_2999_:
{
lean_object* v_idx_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_idx_3001_ = lean_nat_abs(v___y_3000_);
lean_dec(v___y_3000_);
lean_inc(v_idx_3001_);
lean_inc_ref(v_xs_2891_);
v___x_3002_ = l_Array_toSubarray___redArg(v_xs_2891_, v___x_2998_, v_idx_3001_);
v___x_3003_ = l_Subarray_copy___redArg(v___x_3002_);
v___x_3004_ = l_Lean_mkAppN(v_f_2890_, v___x_3003_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = lean_array_get_size(v_xs_2891_);
v___x_3006_ = lean_nat_dec_le(v_idx_3001_, v___x_2998_);
if (v___x_3006_ == 0)
{
v___y_2899_ = v___x_3004_;
v_lower_2900_ = v_idx_3001_;
v_upper_2901_ = v___x_3005_;
goto v___jp_2898_;
}
else
{
lean_dec(v_idx_3001_);
v___y_2899_ = v___x_3004_;
v_lower_2900_ = v___x_2998_;
v_upper_2901_ = v___x_3005_;
goto v___jp_2898_;
}
}
v___jp_3007_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v___y_3008_);
v___x_3009_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3010_ = l_Lean_stringToMessageData(v_tacticName_2888_);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3009_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = lean_array_get_size(v_xs_2891_);
lean_dec_ref(v_xs_2891_);
v___x_3015_ = l_Nat_reprFast(v___x_3014_);
v___x_3016_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
v___x_3017_ = l_Lean_MessageData_ofFormat(v___x_3016_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3013_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3020_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
v___jp_3031_:
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_int_dec_lt(v___y_3032_, v___x_3030_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3034_ = lean_array_get_size(v_xs_2891_);
v___x_3035_ = lean_nat_to_int(v___x_3034_);
v___x_3036_ = lean_int_dec_le(v___x_3035_, v___y_3032_);
lean_dec(v___x_3035_);
if (v___x_3036_ == 0)
{
lean_dec_ref(v_tacticName_2888_);
v___y_3000_ = v___y_3032_;
goto v___jp_2999_;
}
else
{
lean_dec_ref(v_f_2890_);
v___y_3008_ = v___y_3032_;
goto v___jp_3007_;
}
}
else
{
lean_dec_ref(v_f_2890_);
v___y_3008_ = v___y_3032_;
goto v___jp_3007_;
}
}
}
v___jp_2898_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2902_ = l_Array_toSubarray___redArg(v_xs_2891_, v_lower_2900_, v_upper_2901_);
v___x_2903_ = l_Subarray_copy___redArg(v___x_2902_);
v___x_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___y_2899_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
v___jp_2906_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = l_Array_toSubarray___redArg(v_xs_2891_, v_lower_2908_, v_upper_2909_);
v___x_2911_ = l_Subarray_copy___redArg(v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___y_2907_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object* v_tacticName_3043_, lean_object* v_explicit_3044_, lean_object* v_f_3045_, lean_object* v_xs_3046_, lean_object* v_i_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
uint8_t v_explicit_boxed_3053_; lean_object* v_res_3054_; 
v_explicit_boxed_3053_ = lean_unbox(v_explicit_3044_);
v_res_3054_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3043_, v_explicit_boxed_3053_, v_f_3045_, v_xs_3046_, v_i_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_i_3047_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object* v_upperBound_3055_, lean_object* v_xs_3056_, lean_object* v_inst_3057_, lean_object* v_R_3058_, lean_object* v_a_3059_, lean_object* v_b_3060_, lean_object* v_c_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_3055_, v_xs_3056_, v_a_3059_, v_b_3060_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object* v_upperBound_3068_, lean_object* v_xs_3069_, lean_object* v_inst_3070_, lean_object* v_R_3071_, lean_object* v_a_3072_, lean_object* v_b_3073_, lean_object* v_c_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(v_upperBound_3068_, v_xs_3069_, v_inst_3070_, v_R_3071_, v_a_3072_, v_b_3073_, v_c_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v_xs_3069_);
lean_dec(v_upperBound_3068_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object* v_tacticName_3081_, uint8_t v_explicit_3082_, lean_object* v_i_3083_, lean_object* v_mvarId_3084_, lean_object* v_snd_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
if (lean_obj_tag(v_x_3086_) == 5)
{
lean_object* v_fn_3094_; lean_object* v_arg_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v_fn_3094_ = lean_ctor_get(v_x_3086_, 0);
lean_inc_ref(v_fn_3094_);
v_arg_3095_ = lean_ctor_get(v_x_3086_, 1);
lean_inc_ref(v_arg_3095_);
lean_dec_ref_known(v_x_3086_, 2);
v___x_3096_ = lean_array_set(v_x_3087_, v_x_3088_, v_arg_3095_);
v___x_3097_ = lean_unsigned_to_nat(1u);
v___x_3098_ = lean_nat_sub(v_x_3088_, v___x_3097_);
lean_dec(v_x_3088_);
v_x_3086_ = v_fn_3094_;
v_x_3087_ = v___x_3096_;
v_x_3088_ = v___x_3098_;
goto _start;
}
else
{
lean_object* v___x_3100_; 
lean_dec(v_x_3088_);
lean_inc_ref(v_tacticName_3081_);
v___x_3100_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3081_, v_explicit_3082_, v_x_3086_, v_x_3087_, v_i_3083_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v_fst_3102_; lean_object* v_snd_3103_; lean_object* v___x_3104_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v_fst_3102_ = lean_ctor_get(v_a_3101_, 0);
lean_inc(v_fst_3102_);
v_snd_3103_ = lean_ctor_get(v_a_3101_, 1);
lean_inc(v_snd_3103_);
lean_dec(v_a_3101_);
lean_inc(v_mvarId_3084_);
v___x_3104_ = l_Lean_MVarId_getTag(v_mvarId_3084_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
lean_inc_ref(v_tacticName_3081_);
v___x_3106_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_3081_, v_a_3105_, v_fst_3102_, v_snd_3103_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v_snd_3108_; lean_object* v_fst_3109_; lean_object* v_fst_3110_; lean_object* v_snd_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3137_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v_snd_3108_ = lean_ctor_get(v_a_3107_, 1);
lean_inc(v_snd_3108_);
v_fst_3109_ = lean_ctor_get(v_a_3107_, 0);
lean_inc(v_fst_3109_);
lean_dec(v_a_3107_);
v_fst_3110_ = lean_ctor_get(v_snd_3108_, 0);
v_snd_3111_ = lean_ctor_get(v_snd_3108_, 1);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_snd_3108_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3113_ = v_snd_3108_;
v_isShared_3114_ = v_isSharedCheck_3137_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_snd_3111_);
lean_inc(v_fst_3110_);
lean_dec(v_snd_3108_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3137_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; 
lean_inc(v_fst_3109_);
v___x_3115_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_3081_, v_snd_3085_, v_fst_3109_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref_known(v___x_3115_, 1);
v___x_3116_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_3084_, v_fst_3109_, v___y_3090_);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3116_, 0);
lean_dec(v_unused_3128_);
v___x_3118_ = v___x_3116_;
v_isShared_3119_ = v_isSharedCheck_3127_;
goto v_resetjp_3117_;
}
else
{
lean_dec(v___x_3116_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3127_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3120_ = lean_array_to_list(v_snd_3111_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set_tag(v___x_3113_, 1);
lean_ctor_set(v___x_3113_, 1, v___x_3120_);
v___x_3122_ = v___x_3113_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_fst_3110_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3120_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v___x_3122_);
v___x_3124_ = v___x_3118_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_del_object(v___x_3113_);
lean_dec(v_snd_3111_);
lean_dec(v_fst_3110_);
lean_dec(v_fst_3109_);
lean_dec(v_mvarId_3084_);
v_a_3129_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3115_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3115_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v_snd_3085_);
lean_dec(v_mvarId_3084_);
lean_dec_ref(v_tacticName_3081_);
v_a_3138_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3106_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3106_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_snd_3103_);
lean_dec(v_fst_3102_);
lean_dec_ref(v_snd_3085_);
lean_dec(v_mvarId_3084_);
lean_dec_ref(v_tacticName_3081_);
v_a_3146_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3104_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3104_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v_snd_3085_);
lean_dec(v_mvarId_3084_);
lean_dec_ref(v_tacticName_3081_);
v_a_3154_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3100_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3100_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object* v_tacticName_3162_, lean_object* v_explicit_3163_, lean_object* v_i_3164_, lean_object* v_mvarId_3165_, lean_object* v_snd_3166_, lean_object* v_x_3167_, lean_object* v_x_3168_, lean_object* v_x_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
uint8_t v_explicit_boxed_3175_; lean_object* v_res_3176_; 
v_explicit_boxed_3175_ = lean_unbox(v_explicit_3163_);
v_res_3176_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3162_, v_explicit_boxed_3175_, v_i_3164_, v_mvarId_3165_, v_snd_3166_, v_x_3167_, v_x_3168_, v_x_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v_i_3164_);
return v_res_3176_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_unsigned_to_nat(2u);
v___x_3178_ = lean_nat_to_int(v___x_3177_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3180_ = lean_int_neg(v___x_3179_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2));
v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4));
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object* v_mvarId_3187_, lean_object* v_tacticName_3188_, uint8_t v_explicit_3189_, lean_object* v_i_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; 
lean_inc(v_mvarId_3187_);
v___x_3196_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_3187_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v_fst_3198_; lean_object* v_snd_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3258_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v_fst_3198_ = lean_ctor_get(v_a_3197_, 0);
v_snd_3199_ = lean_ctor_get(v_a_3197_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_a_3197_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3201_ = v_a_3197_;
v_isShared_3202_ = v_isSharedCheck_3258_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_snd_3199_);
lean_inc(v_fst_3198_);
lean_dec(v_a_3197_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3258_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v_a_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; uint8_t v___y_3236_; 
v___x_3203_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_3198_, v___y_3192_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = l_Lean_Expr_cleanupAnnotations(v_a_3204_);
v___x_3206_ = l_Lean_Expr_isForall(v___x_3205_);
if (v___x_3206_ == 0)
{
uint8_t v___x_3239_; 
lean_del_object(v___x_3201_);
v___x_3239_ = l_Lean_Expr_isApp(v___x_3205_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
lean_dec(v_snd_3199_);
lean_dec(v_mvarId_3187_);
v___x_3240_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3241_ = l_Lean_stringToMessageData(v_tacticName_3188_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = l_Lean_indentExpr(v___x_3205_);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3246_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
return v___x_3247_;
}
else
{
lean_object* v_dummy_3248_; lean_object* v_nargs_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v_dummy_3248_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_3249_ = l_Lean_Expr_getAppNumArgs(v___x_3205_);
lean_inc(v_nargs_3249_);
v___x_3250_ = lean_mk_array(v_nargs_3249_, v_dummy_3248_);
v___x_3251_ = lean_unsigned_to_nat(1u);
v___x_3252_ = lean_nat_sub(v_nargs_3249_, v___x_3251_);
lean_dec(v_nargs_3249_);
v___x_3253_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3188_, v_explicit_3189_, v_i_3190_, v_mvarId_3187_, v_snd_3199_, v___x_3205_, v___x_3250_, v___x_3252_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
return v___x_3253_;
}
}
else
{
lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3254_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3255_ = lean_int_dec_lt(v_i_3190_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; uint8_t v___x_3257_; 
v___x_3256_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3257_ = lean_int_dec_eq(v_i_3190_, v___x_3256_);
v___y_3236_ = v___x_3257_;
goto v___jp_3235_;
}
else
{
v___y_3236_ = v___x_3206_;
goto v___jp_3235_;
}
}
v___jp_3207_:
{
lean_object* v___x_3212_; uint8_t v___x_3213_; 
v___x_3212_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3213_ = lean_int_dec_eq(v_i_3190_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3215_ = lean_int_dec_eq(v_i_3190_, v___x_3214_);
v___x_3216_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3188_, v___x_3215_, v_mvarId_3187_, v___x_3205_, v_snd_3199_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3188_, v___x_3206_, v_mvarId_3187_, v___x_3205_, v_snd_3199_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3217_;
}
}
v___jp_3218_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3219_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3220_ = l_Lean_stringToMessageData(v_tacticName_3188_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set_tag(v___x_3201_, 7);
lean_ctor_set(v___x_3201_, 1, v___x_3220_);
lean_ctor_set(v___x_3201_, 0, v___x_3219_);
v___x_3222_ = v___x_3201_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
v___x_3223_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3224_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
v___jp_3235_:
{
if (v___y_3236_ == 0)
{
lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3237_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3238_ = lean_int_dec_lt(v___x_3237_, v_i_3190_);
if (v___x_3238_ == 0)
{
lean_del_object(v___x_3201_);
v___y_3208_ = v___y_3191_;
v___y_3209_ = v___y_3192_;
v___y_3210_ = v___y_3193_;
v___y_3211_ = v___y_3194_;
goto v___jp_3207_;
}
else
{
lean_dec_ref(v___x_3205_);
lean_dec(v_snd_3199_);
lean_dec(v_mvarId_3187_);
goto v___jp_3218_;
}
}
else
{
lean_dec_ref(v___x_3205_);
lean_dec(v_snd_3199_);
lean_dec(v_mvarId_3187_);
goto v___jp_3218_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec_ref(v_tacticName_3188_);
lean_dec(v_mvarId_3187_);
v_a_3259_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3196_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3196_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object* v_mvarId_3267_, lean_object* v_tacticName_3268_, lean_object* v_explicit_3269_, lean_object* v_i_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v_explicit_boxed_3276_; lean_object* v_res_3277_; 
v_explicit_boxed_3276_ = lean_unbox(v_explicit_3269_);
v_res_3277_ = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(v_mvarId_3267_, v_tacticName_3268_, v_explicit_boxed_3276_, v_i_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_i_3270_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object* v_tacticName_3278_, lean_object* v_mvarId_3279_, lean_object* v_i_3280_, uint8_t v_explicit_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v___x_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; 
v___x_3287_ = lean_box(v_explicit_3281_);
lean_inc(v_mvarId_3279_);
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3288_, 0, v_mvarId_3279_);
lean_closure_set(v___f_3288_, 1, v_tacticName_3278_);
lean_closure_set(v___f_3288_, 2, v___x_3287_);
lean_closure_set(v___f_3288_, 3, v_i_3280_);
v___x_3289_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_3279_, v___f_3288_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object* v_tacticName_3290_, lean_object* v_mvarId_3291_, lean_object* v_i_3292_, lean_object* v_explicit_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
uint8_t v_explicit_boxed_3299_; lean_object* v_res_3300_; 
v_explicit_boxed_3299_ = lean_unbox(v_explicit_3293_);
v_res_3300_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3290_, v_mvarId_3291_, v_i_3292_, v_explicit_boxed_3299_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_a_3295_);
lean_dec_ref(v_a_3294_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object* v_tacticName_3301_, lean_object* v_i_3302_, uint8_t v_explicit_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3310_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3311_ = lean_int_dec_eq(v_i_3302_, v___x_3310_);
if (v___x_3311_ == 0)
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_a_3313_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3314_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3301_, v_a_3313_, v_i_3302_, v_explicit_3303_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref_known(v___x_3314_, 1);
v___x_3316_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3315_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3316_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
v_a_3317_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3314_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3314_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_i_3302_);
lean_dec_ref(v_tacticName_3301_);
v_a_3325_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3312_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3312_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v___x_3333_; 
lean_dec(v_i_3302_);
lean_dec_ref(v_tacticName_3301_);
v___x_3333_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3335_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v___x_3335_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_a_3334_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3338_, 0, v_a_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3338_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3339_;
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
v_a_3340_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3335_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3335_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
v_a_3348_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3333_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3333_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object* v_tacticName_3356_, lean_object* v_i_3357_, lean_object* v_explicit_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
uint8_t v_explicit_boxed_3365_; lean_object* v_res_3366_; 
v_explicit_boxed_3365_ = lean_unbox(v_explicit_3358_);
v_res_3366_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3356_, v_i_3357_, v_explicit_boxed_3365_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object* v_tacticName_3367_, lean_object* v_i_3368_, uint8_t v_explicit_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3367_, v_i_3368_, v_explicit_3369_, v_a_3371_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object* v_tacticName_3380_, lean_object* v_i_3381_, lean_object* v_explicit_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
uint8_t v_explicit_boxed_3392_; lean_object* v_res_3393_; 
v_explicit_boxed_3392_ = lean_unbox(v_explicit_3382_);
v_res_3393_ = l_Lean_Elab_Tactic_Conv_evalArg(v_tacticName_3380_, v_i_3381_, v_explicit_boxed_3392_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
return v_res_3393_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_box(0);
v___x_3395_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg(){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0);
v___x_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object* v_00_u03b1_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object* v_00_u03b1_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(v_00_u03b1_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object* v_stx_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___x_3451_; lean_object* v___y_3453_; lean_object* v___y_3454_; uint8_t v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; uint8_t v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3451_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_3475_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
lean_inc(v_stx_3441_);
v___x_3476_ = l_Lean_Syntax_isOfKind(v_stx_3441_, v___x_3475_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_dec(v_stx_3441_);
v___x_3477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3477_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___y_3481_; lean_object* v_neg_x3f_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v___x_3478_ = lean_unsigned_to_nat(1u);
v___x_3479_ = l_Lean_Syntax_getArg(v_stx_3441_, v___x_3478_);
lean_dec(v_stx_3441_);
v___x_3499_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__5));
lean_inc(v___x_3479_);
v___x_3500_ = l_Lean_Syntax_isOfKind(v___x_3479_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
lean_dec(v___x_3479_);
v___x_3501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; lean_object* v_tk_x3f_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3502_ = lean_unsigned_to_nat(0u);
v___x_3520_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3502_);
v___x_3521_ = l_Lean_Syntax_isNone(v___x_3520_);
if (v___x_3521_ == 0)
{
uint8_t v___x_3522_; 
lean_inc(v___x_3520_);
v___x_3522_ = l_Lean_Syntax_matchesNull(v___x_3520_, v___x_3478_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec(v___x_3520_);
lean_dec(v___x_3479_);
v___x_3523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3523_;
}
else
{
lean_object* v_tk_x3f_3524_; lean_object* v___x_3525_; 
v_tk_x3f_3524_ = l_Lean_Syntax_getArg(v___x_3520_, v___x_3502_);
lean_dec(v___x_3520_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_tk_x3f_3524_);
v_tk_x3f_3504_ = v___x_3525_;
v___y_3505_ = v_a_3442_;
v___y_3506_ = v_a_3443_;
v___y_3507_ = v_a_3444_;
v___y_3508_ = v_a_3445_;
v___y_3509_ = v_a_3446_;
v___y_3510_ = v_a_3447_;
v___y_3511_ = v_a_3448_;
v___y_3512_ = v_a_3449_;
goto v___jp_3503_;
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3520_);
v___x_3526_ = lean_box(0);
v_tk_x3f_3504_ = v___x_3526_;
v___y_3505_ = v_a_3442_;
v___y_3506_ = v_a_3443_;
v___y_3507_ = v_a_3444_;
v___y_3508_ = v_a_3445_;
v___y_3509_ = v_a_3446_;
v___y_3510_ = v_a_3447_;
v___y_3511_ = v_a_3448_;
v___y_3512_ = v_a_3449_;
goto v___jp_3503_;
}
v___jp_3503_:
{
lean_object* v___x_3513_; uint8_t v___x_3514_; 
v___x_3513_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3478_);
v___x_3514_ = l_Lean_Syntax_isNone(v___x_3513_);
if (v___x_3514_ == 0)
{
uint8_t v___x_3515_; 
lean_inc(v___x_3513_);
v___x_3515_ = l_Lean_Syntax_matchesNull(v___x_3513_, v___x_3478_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; 
lean_dec(v___x_3513_);
lean_dec(v_tk_x3f_3504_);
lean_dec(v___x_3479_);
v___x_3516_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3516_;
}
else
{
lean_object* v_neg_x3f_3517_; lean_object* v___x_3518_; 
v_neg_x3f_3517_ = l_Lean_Syntax_getArg(v___x_3513_, v___x_3502_);
lean_dec(v___x_3513_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v_neg_x3f_3517_);
v___y_3481_ = v_tk_x3f_3504_;
v_neg_x3f_3482_ = v___x_3518_;
v___y_3483_ = v___y_3505_;
v___y_3484_ = v___y_3506_;
v___y_3485_ = v___y_3507_;
v___y_3486_ = v___y_3508_;
v___y_3487_ = v___y_3509_;
v___y_3488_ = v___y_3510_;
v___y_3489_ = v___y_3511_;
v___y_3490_ = v___y_3512_;
goto v___jp_3480_;
}
}
else
{
lean_object* v___x_3519_; 
lean_dec(v___x_3513_);
v___x_3519_ = lean_box(0);
v___y_3481_ = v_tk_x3f_3504_;
v_neg_x3f_3482_ = v___x_3519_;
v___y_3483_ = v___y_3505_;
v___y_3484_ = v___y_3506_;
v___y_3485_ = v___y_3507_;
v___y_3486_ = v___y_3508_;
v___y_3487_ = v___y_3509_;
v___y_3488_ = v___y_3510_;
v___y_3489_ = v___y_3511_;
v___y_3490_ = v___y_3512_;
goto v___jp_3480_;
}
}
}
v___jp_3480_:
{
lean_object* v___x_3491_; lean_object* v_i_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3491_ = lean_unsigned_to_nat(2u);
v_i_3492_ = l_Lean_Syntax_getArg(v___x_3479_, v___x_3491_);
lean_dec(v___x_3479_);
v___x_3493_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__3));
lean_inc(v_i_3492_);
v___x_3494_ = l_Lean_Syntax_isOfKind(v_i_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
lean_dec(v_i_3492_);
lean_dec(v_neg_x3f_3482_);
lean_dec(v___y_3481_);
v___x_3495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3495_;
}
else
{
if (lean_obj_tag(v_neg_x3f_3482_) == 0)
{
v___y_3465_ = v___y_3487_;
v___y_3466_ = v___y_3490_;
v___y_3467_ = v___y_3481_;
v___y_3468_ = v___y_3489_;
v___y_3469_ = v___x_3494_;
v___y_3470_ = v_i_3492_;
v___y_3471_ = v___y_3484_;
v___y_3472_ = v___y_3488_;
goto v___jp_3464_;
}
else
{
lean_dec_ref_known(v_neg_x3f_3482_, 1);
if (v___x_3494_ == 0)
{
v___y_3465_ = v___y_3487_;
v___y_3466_ = v___y_3490_;
v___y_3467_ = v___y_3481_;
v___y_3468_ = v___y_3489_;
v___y_3469_ = v___x_3494_;
v___y_3470_ = v_i_3492_;
v___y_3471_ = v___y_3484_;
v___y_3472_ = v___y_3488_;
goto v___jp_3464_;
}
else
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = l_Lean_TSyntax_getNat(v_i_3492_);
lean_dec(v_i_3492_);
v___x_3497_ = lean_nat_to_int(v___x_3496_);
v___x_3498_ = lean_int_neg(v___x_3497_);
lean_dec(v___x_3497_);
v___y_3453_ = v___y_3487_;
v___y_3454_ = v___y_3490_;
v___y_3455_ = v___x_3494_;
v___y_3456_ = v___y_3489_;
v___y_3457_ = v___y_3481_;
v___y_3458_ = v___y_3484_;
v___y_3459_ = v___y_3488_;
v___y_3460_ = v___x_3498_;
goto v___jp_3452_;
}
}
}
}
}
v___jp_3452_:
{
if (lean_obj_tag(v___y_3457_) == 0)
{
uint8_t v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = 0;
v___x_3462_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3451_, v___y_3460_, v___x_3461_, v___y_3458_, v___y_3453_, v___y_3459_, v___y_3456_, v___y_3454_);
return v___x_3462_;
}
else
{
lean_object* v___x_3463_; 
lean_dec_ref_known(v___y_3457_, 1);
v___x_3463_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3451_, v___y_3460_, v___y_3455_, v___y_3458_, v___y_3453_, v___y_3459_, v___y_3456_, v___y_3454_);
return v___x_3463_;
}
}
v___jp_3464_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3473_ = l_Lean_TSyntax_getNat(v___y_3470_);
lean_dec(v___y_3470_);
v___x_3474_ = lean_nat_to_int(v___x_3473_);
v___y_3453_ = v___y_3465_;
v___y_3454_ = v___y_3466_;
v___y_3455_ = v___y_3469_;
v___y_3456_ = v___y_3468_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v___y_3471_;
v___y_3459_ = v___y_3472_;
v___y_3460_ = v___x_3474_;
goto v___jp_3452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object* v_stx_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Elab_Tactic_Conv_elabArg(v_stx_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1(){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3546_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3547_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
v___x_3548_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1));
v___x_3549_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_elabArg___boxed), 10, 0);
v___x_3550_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3546_, v___x_3547_, v___x_3548_, v___x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object* v_a_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; lean_object* v___x_3563_; 
v___x_3560_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0));
v___x_3561_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3562_ = 0;
v___x_3563_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3560_, v___x_3561_, v___x_3562_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object* v_x_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3573_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object* v_x_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Elab_Tactic_Conv_evalLhs(v_x_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
lean_dec(v_a_3586_);
lean_dec_ref(v_a_3585_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_x_3582_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1(){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3607_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0));
v___x_3609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3610_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLhs___boxed), 10, 0);
v___x_3611_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3607_, v___x_3608_, v___x_3609_, v___x_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object* v_a_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3(){
_start:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6));
v___x_3642_ = l_Lean_addBuiltinDeclarationRanges(v___x_3640_, v___x_3641_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object* v_a_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
return v_res_3644_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3647_ = lean_int_neg(v___x_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; uint8_t v___x_3656_; lean_object* v___x_3657_; 
v___x_3654_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0));
v___x_3655_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1, &l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1);
v___x_3656_ = 0;
v___x_3657_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3654_, v___x_3655_, v___x_3656_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object* v_x_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3667_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object* v_x_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l_Lean_Elab_Tactic_Conv_evalRhs(v_x_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_a_3677_);
lean_dec(v_x_3676_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1(){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3701_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0));
v___x_3703_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3704_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRhs___boxed), 10, 0);
v___x_3705_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3701_, v___x_3702_, v___x_3703_, v___x_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object* v_a_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3(){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3735_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6));
v___x_3736_ = l_Lean_addBuiltinDeclarationRanges(v___x_3734_, v___x_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object* v_e_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v___x_3742_; 
v___x_3742_ = l_Lean_Expr_hasMVar(v_e_3739_);
if (v___x_3742_ == 0)
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v_e_3739_);
return v___x_3743_;
}
else
{
lean_object* v___x_3744_; lean_object* v_mctx_3745_; lean_object* v___x_3746_; lean_object* v_fst_3747_; lean_object* v_snd_3748_; lean_object* v___x_3749_; lean_object* v_cache_3750_; lean_object* v_zetaDeltaFVarIds_3751_; lean_object* v_postponed_3752_; lean_object* v_diag_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3762_; 
v___x_3744_ = lean_st_ref_get(v___y_3740_);
v_mctx_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc_ref(v_mctx_3745_);
lean_dec(v___x_3744_);
v___x_3746_ = l_Lean_instantiateMVarsCore(v_mctx_3745_, v_e_3739_);
v_fst_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_fst_3747_);
v_snd_3748_ = lean_ctor_get(v___x_3746_, 1);
lean_inc(v_snd_3748_);
lean_dec_ref(v___x_3746_);
v___x_3749_ = lean_st_ref_take(v___y_3740_);
v_cache_3750_ = lean_ctor_get(v___x_3749_, 1);
v_zetaDeltaFVarIds_3751_ = lean_ctor_get(v___x_3749_, 2);
v_postponed_3752_ = lean_ctor_get(v___x_3749_, 3);
v_diag_3753_ = lean_ctor_get(v___x_3749_, 4);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v___x_3749_, 0);
lean_dec(v_unused_3763_);
v___x_3755_ = v___x_3749_;
v_isShared_3756_ = v_isSharedCheck_3762_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_diag_3753_);
lean_inc(v_postponed_3752_);
lean_inc(v_zetaDeltaFVarIds_3751_);
lean_inc(v_cache_3750_);
lean_dec(v___x_3749_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3762_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v_snd_3748_);
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_snd_3748_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_cache_3750_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_zetaDeltaFVarIds_3751_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_postponed_3752_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_diag_3753_);
v___x_3758_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_st_ref_set(v___y_3740_, v___x_3758_);
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v_fst_3747_);
return v___x_3760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object* v_e_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3764_, v___y_3765_);
lean_dec(v___y_3765_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object* v_e_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3768_, v___y_3774_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object* v_e_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(v_e_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object* v_x_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v___x_3800_; 
lean_inc(v___y_3794_);
lean_inc_ref(v___y_3793_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
v___x_3800_ = lean_apply_9(v_x_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, lean_box(0));
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object* v_x_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(v_x_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object* v_mvarId_3812_, lean_object* v_x_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___f_3823_; lean_object* v___x_3824_; 
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3823_, 0, v_x_3813_);
lean_closure_set(v___f_3823_, 1, v___y_3814_);
lean_closure_set(v___f_3823_, 2, v___y_3815_);
lean_closure_set(v___f_3823_, 3, v___y_3816_);
lean_closure_set(v___f_3823_, 4, v___y_3817_);
v___x_3824_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3812_, v___f_3823_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3824_) == 0)
{
return v___x_3824_;
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object* v_mvarId_3833_, lean_object* v_x_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3833_, v_x_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object* v_00_u03b1_3845_, lean_object* v_mvarId_3846_, lean_object* v_x_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3846_, v_x_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object* v_00_u03b1_3858_, lean_object* v_mvarId_3859_, lean_object* v_x_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(v_00_u03b1_3858_, v_mvarId_3859_, v_x_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object* v_msg_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_ref_3877_; lean_object* v___x_3878_; lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3887_; 
v_ref_3877_ = lean_ctor_get(v___y_3874_, 5);
v___x_3878_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3887_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3887_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v___x_3885_; 
lean_inc(v_ref_3877_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v_ref_3877_);
lean_ctor_set(v___x_3883_, 1, v_a_3879_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 1);
lean_ctor_set(v___x_3881_, 0, v___x_3883_);
v___x_3885_ = v___x_3881_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object* v_msg_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object* v_mvarId_3895_, lean_object* v_val_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; lean_object* v_mctx_3900_; lean_object* v_cache_3901_; lean_object* v_zetaDeltaFVarIds_3902_; lean_object* v_postponed_3903_; lean_object* v_diag_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3932_; 
v___x_3899_ = lean_st_ref_take(v___y_3897_);
v_mctx_3900_ = lean_ctor_get(v___x_3899_, 0);
v_cache_3901_ = lean_ctor_get(v___x_3899_, 1);
v_zetaDeltaFVarIds_3902_ = lean_ctor_get(v___x_3899_, 2);
v_postponed_3903_ = lean_ctor_get(v___x_3899_, 3);
v_diag_3904_ = lean_ctor_get(v___x_3899_, 4);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3906_ = v___x_3899_;
v_isShared_3907_ = v_isSharedCheck_3932_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_diag_3904_);
lean_inc(v_postponed_3903_);
lean_inc(v_zetaDeltaFVarIds_3902_);
lean_inc(v_cache_3901_);
lean_inc(v_mctx_3900_);
lean_dec(v___x_3899_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3932_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v_depth_3908_; lean_object* v_levelAssignDepth_3909_; lean_object* v_lmvarCounter_3910_; lean_object* v_mvarCounter_3911_; lean_object* v_lDecls_3912_; lean_object* v_decls_3913_; lean_object* v_userNames_3914_; lean_object* v_lAssignment_3915_; lean_object* v_eAssignment_3916_; lean_object* v_dAssignment_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3931_; 
v_depth_3908_ = lean_ctor_get(v_mctx_3900_, 0);
v_levelAssignDepth_3909_ = lean_ctor_get(v_mctx_3900_, 1);
v_lmvarCounter_3910_ = lean_ctor_get(v_mctx_3900_, 2);
v_mvarCounter_3911_ = lean_ctor_get(v_mctx_3900_, 3);
v_lDecls_3912_ = lean_ctor_get(v_mctx_3900_, 4);
v_decls_3913_ = lean_ctor_get(v_mctx_3900_, 5);
v_userNames_3914_ = lean_ctor_get(v_mctx_3900_, 6);
v_lAssignment_3915_ = lean_ctor_get(v_mctx_3900_, 7);
v_eAssignment_3916_ = lean_ctor_get(v_mctx_3900_, 8);
v_dAssignment_3917_ = lean_ctor_get(v_mctx_3900_, 9);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_mctx_3900_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3919_ = v_mctx_3900_;
v_isShared_3920_ = v_isSharedCheck_3931_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_dAssignment_3917_);
lean_inc(v_eAssignment_3916_);
lean_inc(v_lAssignment_3915_);
lean_inc(v_userNames_3914_);
lean_inc(v_decls_3913_);
lean_inc(v_lDecls_3912_);
lean_inc(v_mvarCounter_3911_);
lean_inc(v_lmvarCounter_3910_);
lean_inc(v_levelAssignDepth_3909_);
lean_inc(v_depth_3908_);
lean_dec(v_mctx_3900_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3931_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
v___x_3921_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_3916_, v_mvarId_3895_, v_val_3896_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 8, v___x_3921_);
v___x_3923_ = v___x_3919_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_depth_3908_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_levelAssignDepth_3909_);
lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_lmvarCounter_3910_);
lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_mvarCounter_3911_);
lean_ctor_set(v_reuseFailAlloc_3930_, 4, v_lDecls_3912_);
lean_ctor_set(v_reuseFailAlloc_3930_, 5, v_decls_3913_);
lean_ctor_set(v_reuseFailAlloc_3930_, 6, v_userNames_3914_);
lean_ctor_set(v_reuseFailAlloc_3930_, 7, v_lAssignment_3915_);
lean_ctor_set(v_reuseFailAlloc_3930_, 8, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3930_, 9, v_dAssignment_3917_);
v___x_3923_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3925_; 
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3923_);
v___x_3925_ = v___x_3906_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_cache_3901_);
lean_ctor_set(v_reuseFailAlloc_3929_, 2, v_zetaDeltaFVarIds_3902_);
lean_ctor_set(v_reuseFailAlloc_3929_, 3, v_postponed_3903_);
lean_ctor_set(v_reuseFailAlloc_3929_, 4, v_diag_3904_);
v___x_3925_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_st_ref_set(v___y_3897_, v___x_3925_);
v___x_3927_ = lean_box(0);
v___x_3928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
return v___x_3928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object* v_mvarId_3933_, lean_object* v_val_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_3933_, v_val_3934_, v___y_3935_);
lean_dec(v___y_3935_);
return v_res_3937_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1));
v___x_3941_ = l_Lean_stringToMessageData(v___x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object* v_a_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v___x_3952_; 
lean_inc(v_a_3942_);
v___x_3952_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_3942_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v_fst_3954_; lean_object* v_snd_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_4007_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v_fst_3954_ = lean_ctor_get(v_a_3953_, 0);
v_snd_3955_ = lean_ctor_get(v_a_3953_, 1);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_a_3953_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3957_ = v_a_3953_;
v_isShared_3958_ = v_isSharedCheck_4007_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_snd_3955_);
lean_inc(v_fst_3954_);
lean_dec(v_a_3953_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_4007_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v_a_3960_; lean_object* v___x_3961_; 
v___x_3959_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_fst_3954_, v___y_3948_);
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref(v___x_3959_);
v___x_3961_ = l_Lean_Expr_cleanupAnnotations(v_a_3960_);
if (lean_obj_tag(v___x_3961_) == 5)
{
lean_object* v_fn_3962_; lean_object* v_arg_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_del_object(v___x_3957_);
v_fn_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc_ref(v_fn_3962_);
v_arg_3963_ = lean_ctor_get(v___x_3961_, 1);
lean_inc_ref(v_arg_3963_);
lean_dec_ref_known(v___x_3961_, 2);
v___x_3964_ = lean_box(0);
v___x_3965_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fn_3962_, v___x_3964_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v_fst_3967_; lean_object* v_snd_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3992_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v_fst_3967_ = lean_ctor_get(v_a_3966_, 0);
v_snd_3968_ = lean_ctor_get(v_a_3966_, 1);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_a_3966_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3970_ = v_a_3966_;
v_isShared_3971_ = v_isSharedCheck_3992_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_snd_3968_);
lean_inc(v_fst_3967_);
lean_dec(v_a_3966_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3992_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; 
lean_inc_ref(v_arg_3963_);
lean_inc(v_snd_3968_);
v___x_3972_ = l_Lean_Meta_mkCongrFun(v_snd_3968_, v_arg_3963_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_a_3942_, v_a_3973_, v___y_3948_);
lean_dec_ref(v___x_3974_);
v___x_3975_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0));
v___x_3976_ = l_Lean_Expr_app___override(v_fst_3967_, v_arg_3963_);
v___x_3977_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_3975_, v_snd_3955_, v___x_3976_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3981_; 
lean_dec_ref_known(v___x_3977_, 1);
v___x_3978_ = l_Lean_Expr_mvarId_x21(v_snd_3968_);
lean_dec(v_snd_3968_);
v___x_3979_ = lean_box(0);
if (v_isShared_3971_ == 0)
{
lean_ctor_set_tag(v___x_3970_, 1);
lean_ctor_set(v___x_3970_, 1, v___x_3979_);
lean_ctor_set(v___x_3970_, 0, v___x_3978_);
v___x_3981_ = v___x_3970_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3981_, v___y_3944_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
return v___x_3982_;
}
}
else
{
lean_del_object(v___x_3970_);
lean_dec(v_snd_3968_);
return v___x_3977_;
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_del_object(v___x_3970_);
lean_dec(v_snd_3968_);
lean_dec(v_fst_3967_);
lean_dec_ref(v_arg_3963_);
lean_dec(v_snd_3955_);
lean_dec(v_a_3942_);
v_a_3984_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3972_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3972_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v_arg_3963_);
lean_dec(v_snd_3955_);
lean_dec(v_a_3942_);
v_a_3993_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3965_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3965_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4004_; 
lean_dec(v_snd_3955_);
lean_dec(v_a_3942_);
v___x_4001_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2);
v___x_4002_ = l_Lean_indentExpr(v___x_3961_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set_tag(v___x_3957_, 7);
lean_ctor_set(v___x_3957_, 1, v___x_4002_);
lean_ctor_set(v___x_3957_, 0, v___x_4001_);
v___x_4004_ = v___x_3957_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v___x_4002_);
v___x_4004_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v___x_4004_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
return v___x_4005_;
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v_a_3942_);
v_a_4008_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3952_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3952_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object* v_a_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(v_a_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4028_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___f_4038_; lean_object* v___x_4039_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc_n(v_a_4037_, 2);
lean_dec_ref_known(v___x_4036_, 1);
v___f_4038_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4038_, 0, v_a_4037_);
v___x_4039_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_a_4037_, v___f_4038_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
return v___x_4039_;
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v_a_4040_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4036_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4036_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object* v_x_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object* v_x_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_Elab_Tactic_Conv_evalFun(v_x_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
lean_dec(v_a_4073_);
lean_dec_ref(v_a_4072_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
lean_dec(v_x_4069_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object* v_mvarId_4080_, lean_object* v_val_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_4080_, v_val_4081_, v___y_4087_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object* v_mvarId_4092_, lean_object* v_val_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(v_mvarId_4092_, v_val_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object* v_00_u03b1_4104_, lean_object* v_msg_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_4105_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object* v_00_u03b1_4116_, lean_object* v_msg_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(v_00_u03b1_4116_, v_msg_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1(){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4142_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0));
v___x_4144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4145_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___boxed), 10, 0);
v___x_4146_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4142_, v___x_4143_, v___x_4144_, v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3(){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6));
v___x_4177_ = l_Lean_addBuiltinDeclarationRanges(v___x_4175_, v___x_4176_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object* v_a_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
return v_res_4179_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0));
v___x_4182_ = l_Lean_stringToMessageData(v___x_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object* v___x_4183_, lean_object* v_declName_4184_, lean_object* v_type_4185_, lean_object* v_value_4186_, lean_object* v_rhs_4187_, lean_object* v_a_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_inc_ref(v_a_4188_);
v___x_4194_ = l_Lean_Expr_app___override(v___x_4183_, v_a_4188_);
lean_inc(v___y_4192_);
lean_inc_ref(v___y_4191_);
lean_inc(v___y_4190_);
lean_inc_ref(v___y_4189_);
v___x_4195_ = lean_infer_type(v___x_4194_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; uint8_t v___x_4201_; uint8_t v___x_4202_; lean_object* v___x_4203_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc_n(v_a_4196_, 2);
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = lean_unsigned_to_nat(1u);
v___x_4198_ = lean_mk_empty_array_with_capacity(v___x_4197_);
v___x_4199_ = lean_array_push(v___x_4198_, v_a_4188_);
v___x_4200_ = 0;
v___x_4201_ = 1;
v___x_4202_ = 1;
v___x_4203_ = l_Lean_Meta_mkLambdaFVars(v___x_4199_, v_a_4196_, v___x_4200_, v___x_4201_, v___x_4200_, v___x_4201_, v___x_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
lean_inc(v_a_4196_);
v___x_4205_ = l_Lean_Meta_getLevel(v_a_4196_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4207_, 0, v_a_4196_);
v___x_4208_ = 0;
v___x_4209_ = lean_box(0);
v___x_4210_ = l_Lean_Meta_mkFreshExprMVar(v___x_4207_, v___x_4208_, v___x_4209_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4212_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4210_, 1);
v___x_4212_ = l_Lean_Meta_mkLambdaFVars(v___x_4199_, v_a_4211_, v___x_4200_, v___x_4201_, v___x_4200_, v___x_4201_, v___x_4202_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec_ref(v___x_4199_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4246_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4246_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4246_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4223_ = l_Lean_Expr_bindingBody_x21(v_a_4213_);
v___x_4224_ = l_Lean_Expr_letE___override(v_declName_4184_, v_type_4185_, v_value_4186_, v___x_4223_, v___x_4200_);
v___x_4225_ = l_Lean_Meta_isExprDefEq(v_rhs_4187_, v___x_4224_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; uint8_t v___x_4227_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = lean_unbox(v_a_4226_);
lean_dec(v_a_4226_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_del_object(v___x_4215_);
lean_dec(v_a_4213_);
lean_dec(v_a_4206_);
lean_dec(v_a_4204_);
v___x_4228_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1);
v___x_4229_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4228_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4229_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4229_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
else
{
goto v___jp_4217_;
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_del_object(v___x_4215_);
lean_dec(v_a_4213_);
lean_dec(v_a_4206_);
lean_dec(v_a_4204_);
v_a_4238_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4225_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4225_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
v___jp_4217_:
{
lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4221_; 
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v_a_4206_);
lean_ctor_set(v___x_4218_, 1, v_a_4213_);
v___x_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4219_, 0, v_a_4204_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4219_);
v___x_4221_ = v___x_4215_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec(v_a_4206_);
lean_dec(v_a_4204_);
lean_dec_ref(v_rhs_4187_);
lean_dec_ref(v_value_4186_);
lean_dec_ref(v_type_4185_);
lean_dec(v_declName_4184_);
v_a_4247_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4212_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4212_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
lean_dec(v_a_4206_);
lean_dec(v_a_4204_);
lean_dec_ref(v___x_4199_);
lean_dec_ref(v_rhs_4187_);
lean_dec_ref(v_value_4186_);
lean_dec_ref(v_type_4185_);
lean_dec(v_declName_4184_);
v_a_4255_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4257_ = v___x_4210_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4210_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v_a_4204_);
lean_dec_ref(v___x_4199_);
lean_dec(v_a_4196_);
lean_dec_ref(v_rhs_4187_);
lean_dec_ref(v_value_4186_);
lean_dec_ref(v_type_4185_);
lean_dec(v_declName_4184_);
v_a_4263_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4205_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4205_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref(v___x_4199_);
lean_dec(v_a_4196_);
lean_dec_ref(v_rhs_4187_);
lean_dec_ref(v_value_4186_);
lean_dec_ref(v_type_4185_);
lean_dec(v_declName_4184_);
v_a_4271_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4203_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4203_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec_ref(v_a_4188_);
lean_dec_ref(v_rhs_4187_);
lean_dec_ref(v_value_4186_);
lean_dec_ref(v_type_4185_);
lean_dec(v_declName_4184_);
v_a_4279_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4195_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4195_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object* v___x_4287_, lean_object* v_declName_4288_, lean_object* v_type_4289_, lean_object* v_value_4290_, lean_object* v_rhs_4291_, lean_object* v_a_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(v___x_4287_, v_declName_4288_, v_type_4289_, v_value_4290_, v_rhs_4291_, v_a_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object* v___x_4299_, lean_object* v_snd_4300_, lean_object* v_x_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4307_ = lean_unsigned_to_nat(1u);
v___x_4308_ = lean_mk_empty_array_with_capacity(v___x_4307_);
v___x_4309_ = lean_array_push(v___x_4308_, v_x_4301_);
lean_inc_ref_n(v___x_4309_, 2);
v___x_4310_ = l_Lean_Expr_beta(v___x_4299_, v___x_4309_);
v___x_4311_ = l_Lean_Expr_beta(v_snd_4300_, v___x_4309_);
v___x_4312_ = l_Lean_Meta_mkEq(v___x_4310_, v___x_4311_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v___x_4314_ = lean_box(0);
v___x_4315_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4313_, v___x_4314_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; uint8_t v___x_4317_; uint8_t v___x_4318_; uint8_t v___x_4319_; lean_object* v___x_4320_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc_n(v_a_4316_, 2);
lean_dec_ref_known(v___x_4315_, 1);
v___x_4317_ = 0;
v___x_4318_ = 1;
v___x_4319_ = 1;
v___x_4320_ = l_Lean_Meta_mkLambdaFVars(v___x_4309_, v_a_4316_, v___x_4317_, v___x_4318_, v___x_4317_, v___x_4318_, v___x_4319_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
lean_dec_ref(v___x_4309_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4330_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4323_ = v___x_4320_;
v_isShared_4324_ = v_isSharedCheck_4330_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4320_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4330_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4325_ = l_Lean_Expr_mvarId_x21(v_a_4316_);
lean_dec(v_a_4316_);
v___x_4326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4326_, 0, v_a_4321_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 0, v___x_4326_);
v___x_4328_ = v___x_4323_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4326_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_a_4316_);
v_a_4331_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4320_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4320_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v___x_4309_);
v_a_4339_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4315_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4315_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
else
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
lean_dec_ref(v___x_4309_);
v_a_4347_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4312_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4312_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object* v___x_4355_, lean_object* v_snd_4356_, lean_object* v_x_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(v___x_4355_, v_snd_4356_, v_x_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
return v_res_4363_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4368_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2));
v___x_4369_ = l_Lean_stringToMessageData(v___x_4368_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object* v_mvarId_4370_, lean_object* v_lhs_4371_, lean_object* v_rhs_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
if (lean_obj_tag(v_lhs_4371_) == 8)
{
lean_object* v_declName_4378_; lean_object* v_type_4379_; lean_object* v_value_4380_; lean_object* v_body_4381_; lean_object* v___x_4382_; 
v_declName_4378_ = lean_ctor_get(v_lhs_4371_, 0);
lean_inc(v_declName_4378_);
v_type_4379_ = lean_ctor_get(v_lhs_4371_, 1);
lean_inc_ref_n(v_type_4379_, 2);
v_value_4380_ = lean_ctor_get(v_lhs_4371_, 2);
lean_inc_ref(v_value_4380_);
v_body_4381_ = lean_ctor_get(v_lhs_4371_, 3);
lean_inc_ref(v_body_4381_);
lean_dec_ref_known(v_lhs_4371_, 4);
v___x_4382_ = l_Lean_Meta_getLevel(v_type_4379_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; uint8_t v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4382_, 1);
v___x_4384_ = 0;
lean_inc_ref(v_type_4379_);
lean_inc(v_declName_4378_);
v___x_4385_ = l_Lean_mkLambda(v_declName_4378_, v___x_4384_, v_type_4379_, v_body_4381_);
lean_inc_ref(v___x_4385_);
v___x_4386_ = l_Lean_Meta_isTypeCorrect(v___x_4385_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4386_) == 0)
{
lean_object* v_a_4387_; lean_object* v___f_4388_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; uint8_t v___x_4465_; 
v_a_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_a_4387_);
lean_dec_ref_known(v___x_4386_, 1);
lean_inc_ref(v_value_4380_);
lean_inc_ref(v_type_4379_);
lean_inc(v_declName_4378_);
lean_inc_ref(v___x_4385_);
v___f_4388_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4388_, 0, v___x_4385_);
lean_closure_set(v___f_4388_, 1, v_declName_4378_);
lean_closure_set(v___f_4388_, 2, v_type_4379_);
lean_closure_set(v___f_4388_, 3, v_value_4380_);
lean_closure_set(v___f_4388_, 4, v_rhs_4372_);
v___x_4465_ = lean_unbox(v_a_4387_);
lean_dec(v_a_4387_);
if (v___x_4465_ == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v___f_4388_);
lean_dec_ref(v___x_4385_);
lean_dec(v_a_4383_);
lean_dec_ref(v_value_4380_);
lean_dec_ref(v_type_4379_);
lean_dec(v_declName_4378_);
lean_dec(v_mvarId_4370_);
v___x_4466_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3);
v___x_4467_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4466_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4467_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4467_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
else
{
v___y_4390_ = v_a_4373_;
v___y_4391_ = v_a_4374_;
v___y_4392_ = v_a_4375_;
v___y_4393_ = v_a_4376_;
goto v___jp_4389_;
}
v___jp_4389_:
{
lean_object* v___x_4394_; 
lean_inc_ref(v_type_4379_);
lean_inc(v_declName_4378_);
v___x_4394_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4378_, v_type_4379_, v___f_4388_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v_snd_4396_; lean_object* v_fst_4397_; lean_object* v_fst_4398_; lean_object* v_snd_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4456_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v_snd_4396_ = lean_ctor_get(v_a_4395_, 1);
lean_inc(v_snd_4396_);
v_fst_4397_ = lean_ctor_get(v_a_4395_, 0);
lean_inc(v_fst_4397_);
lean_dec(v_a_4395_);
v_fst_4398_ = lean_ctor_get(v_snd_4396_, 0);
v_snd_4399_ = lean_ctor_get(v_snd_4396_, 1);
v_isSharedCheck_4456_ = !lean_is_exclusive(v_snd_4396_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4401_ = v_snd_4396_;
v_isShared_4402_ = v_isSharedCheck_4456_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_snd_4399_);
lean_inc(v_fst_4398_);
lean_dec(v_snd_4396_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4456_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___f_4403_; lean_object* v___x_4404_; 
lean_inc(v_snd_4399_);
lean_inc_ref(v___x_4385_);
v___f_4403_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4403_, 0, v___x_4385_);
lean_closure_set(v___f_4403_, 1, v_snd_4399_);
lean_inc_ref(v_type_4379_);
v___x_4404_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4378_, v_type_4379_, v___f_4403_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; lean_object* v_fst_4406_; lean_object* v_snd_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4447_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v_fst_4406_ = lean_ctor_get(v_a_4405_, 0);
v_snd_4407_ = lean_ctor_get(v_a_4405_, 1);
v_isSharedCheck_4447_ = !lean_is_exclusive(v_a_4405_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4409_ = v_a_4405_;
v_isShared_4410_ = v_isSharedCheck_4447_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_snd_4407_);
lean_inc(v_fst_4406_);
lean_dec(v_a_4405_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4447_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4411_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1));
v___x_4412_ = lean_box(0);
if (v_isShared_4410_ == 0)
{
lean_ctor_set_tag(v___x_4409_, 1);
lean_ctor_set(v___x_4409_, 1, v___x_4412_);
lean_ctor_set(v___x_4409_, 0, v_fst_4398_);
v___x_4414_ = v___x_4409_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v_fst_4398_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v___x_4412_);
v___x_4414_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4416_; 
if (v_isShared_4402_ == 0)
{
lean_ctor_set_tag(v___x_4401_, 1);
lean_ctor_set(v___x_4401_, 1, v___x_4414_);
lean_ctor_set(v___x_4401_, 0, v_a_4383_);
v___x_4416_ = v___x_4401_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4383_);
lean_ctor_set(v_reuseFailAlloc_4445_, 1, v___x_4414_);
v___x_4416_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4443_; 
v___x_4417_ = l_Lean_mkConst(v___x_4411_, v___x_4416_);
v___x_4418_ = l_Lean_mkApp6(v___x_4417_, v_type_4379_, v_fst_4397_, v___x_4385_, v_snd_4399_, v_value_4380_, v_fst_4406_);
v___x_4419_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4370_, v___x_4418_, v___y_4391_);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; 
v_unused_4444_ = lean_ctor_get(v___x_4419_, 0);
lean_dec(v_unused_4444_);
v___x_4421_ = v___x_4419_;
v_isShared_4422_ = v_isSharedCheck_4443_;
goto v_resetjp_4420_;
}
else
{
lean_dec(v___x_4419_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4443_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4407_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4434_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4434_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4434_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4422_ == 0)
{
lean_ctor_set_tag(v___x_4421_, 1);
lean_ctor_set(v___x_4421_, 0, v_a_4424_);
v___x_4429_ = v___x_4421_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
lean_object* v___x_4431_; 
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 0, v___x_4429_);
v___x_4431_ = v___x_4426_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_del_object(v___x_4421_);
v_a_4435_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4423_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4423_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
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
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_del_object(v___x_4401_);
lean_dec(v_snd_4399_);
lean_dec(v_fst_4398_);
lean_dec(v_fst_4397_);
lean_dec_ref(v___x_4385_);
lean_dec(v_a_4383_);
lean_dec_ref(v_value_4380_);
lean_dec_ref(v_type_4379_);
lean_dec(v_mvarId_4370_);
v_a_4448_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4404_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4404_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec_ref(v___x_4385_);
lean_dec(v_a_4383_);
lean_dec_ref(v_value_4380_);
lean_dec_ref(v_type_4379_);
lean_dec(v_declName_4378_);
lean_dec(v_mvarId_4370_);
v_a_4457_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4394_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4394_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref(v___x_4385_);
lean_dec(v_a_4383_);
lean_dec_ref(v_value_4380_);
lean_dec_ref(v_type_4379_);
lean_dec(v_declName_4378_);
lean_dec_ref(v_rhs_4372_);
lean_dec(v_mvarId_4370_);
v_a_4476_ = lean_ctor_get(v___x_4386_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4386_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4386_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
lean_dec_ref(v_body_4381_);
lean_dec_ref(v_value_4380_);
lean_dec_ref(v_type_4379_);
lean_dec(v_declName_4378_);
lean_dec_ref(v_rhs_4372_);
lean_dec(v_mvarId_4370_);
v_a_4484_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4382_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4382_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
lean_dec_ref(v_rhs_4372_);
lean_dec_ref(v_lhs_4371_);
lean_dec(v_mvarId_4370_);
v___x_4492_ = lean_box(0);
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
return v___x_4493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object* v_mvarId_4494_, lean_object* v_lhs_4495_, lean_object* v_rhs_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4494_, v_lhs_4495_, v_rhs_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object* v_body_4504_, lean_object* v_snd_4505_, lean_object* v_b_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4512_ = lean_expr_instantiate1(v_body_4504_, v_b_4506_);
v___x_4513_ = lean_box(0);
v___x_4514_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_4512_, v___x_4513_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v_fst_4516_; lean_object* v_snd_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4579_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v_fst_4516_ = lean_ctor_get(v_a_4515_, 0);
v_snd_4517_ = lean_ctor_get(v_a_4515_, 1);
v_isSharedCheck_4579_ = !lean_is_exclusive(v_a_4515_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4519_ = v_a_4515_;
v_isShared_4520_ = v_isSharedCheck_4579_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_snd_4517_);
lean_inc(v_fst_4516_);
lean_dec(v_a_4515_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4579_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; uint8_t v___x_4524_; uint8_t v___x_4525_; uint8_t v___x_4526_; lean_object* v___x_4527_; 
v___x_4521_ = lean_unsigned_to_nat(1u);
v___x_4522_ = lean_mk_empty_array_with_capacity(v___x_4521_);
v___x_4523_ = lean_array_push(v___x_4522_, v_b_4506_);
v___x_4524_ = 0;
v___x_4525_ = 1;
v___x_4526_ = 1;
lean_inc(v_fst_4516_);
v___x_4527_ = l_Lean_Meta_mkLambdaFVars(v___x_4523_, v_fst_4516_, v___x_4524_, v___x_4525_, v___x_4524_, v___x_4525_, v___x_4526_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4529_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4527_, 1);
lean_inc(v_snd_4517_);
v___x_4529_ = l_Lean_Meta_mkLambdaFVars(v___x_4523_, v_snd_4517_, v___x_4524_, v___x_4525_, v___x_4524_, v___x_4525_, v___x_4526_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4531_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v___x_4531_ = l_Lean_Meta_mkForallFVars(v___x_4523_, v_fst_4516_, v___x_4524_, v___x_4525_, v___x_4525_, v___x_4526_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec_ref(v___x_4523_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v___x_4533_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_4534_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_4533_, v_snd_4505_, v_a_4532_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4545_; 
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4545_ == 0)
{
lean_object* v_unused_4546_; 
v_unused_4546_ = lean_ctor_get(v___x_4534_, 0);
lean_dec(v_unused_4546_);
v___x_4536_ = v___x_4534_;
v_isShared_4537_ = v_isSharedCheck_4545_;
goto v_resetjp_4535_;
}
else
{
lean_dec(v___x_4534_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4545_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4520_ == 0)
{
lean_ctor_set(v___x_4519_, 0, v_a_4530_);
v___x_4539_ = v___x_4519_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4530_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v_snd_4517_);
v___x_4539_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
lean_object* v___x_4540_; lean_object* v___x_4542_; 
v___x_4540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4540_, 0, v_a_4528_);
lean_ctor_set(v___x_4540_, 1, v___x_4539_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v___x_4540_);
v___x_4542_ = v___x_4536_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4540_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec(v_a_4530_);
lean_dec(v_a_4528_);
lean_del_object(v___x_4519_);
lean_dec(v_snd_4517_);
v_a_4547_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4534_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4534_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4530_);
lean_dec(v_a_4528_);
lean_del_object(v___x_4519_);
lean_dec(v_snd_4517_);
lean_dec_ref(v_snd_4505_);
v_a_4555_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4531_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4531_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_a_4528_);
lean_dec_ref(v___x_4523_);
lean_del_object(v___x_4519_);
lean_dec(v_snd_4517_);
lean_dec(v_fst_4516_);
lean_dec_ref(v_snd_4505_);
v_a_4563_ = lean_ctor_get(v___x_4529_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4529_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4529_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4529_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec_ref(v___x_4523_);
lean_del_object(v___x_4519_);
lean_dec(v_snd_4517_);
lean_dec(v_fst_4516_);
lean_dec_ref(v_snd_4505_);
v_a_4571_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4527_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4527_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec_ref(v_b_4506_);
lean_dec_ref(v_snd_4505_);
v_a_4580_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4514_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4514_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object* v_body_4588_, lean_object* v_snd_4589_, lean_object* v_b_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(v_body_4588_, v_snd_4589_, v_b_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec_ref(v_body_4588_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object* v_body_4597_, lean_object* v_snd_4598_, lean_object* v_name_4599_, uint8_t v_bi_4600_, lean_object* v_type_4601_, uint8_t v_kind_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v___f_4608_; lean_object* v___x_4609_; 
v___f_4608_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4608_, 0, v_body_4597_);
lean_closure_set(v___f_4608_, 1, v_snd_4598_);
v___x_4609_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4599_, v_bi_4600_, v_type_4601_, v___f_4608_, v_kind_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
if (lean_obj_tag(v___x_4609_) == 0)
{
lean_object* v_a_4610_; lean_object* v___x_4612_; uint8_t v_isShared_4613_; uint8_t v_isSharedCheck_4617_; 
v_a_4610_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4612_ = v___x_4609_;
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
else
{
lean_inc(v_a_4610_);
lean_dec(v___x_4609_);
v___x_4612_ = lean_box(0);
v_isShared_4613_ = v_isSharedCheck_4617_;
goto v_resetjp_4611_;
}
v_resetjp_4611_:
{
lean_object* v___x_4615_; 
if (v_isShared_4613_ == 0)
{
v___x_4615_ = v___x_4612_;
goto v_reusejp_4614_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
v___x_4615_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4614_;
}
v_reusejp_4614_:
{
return v___x_4615_;
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
v_a_4618_ = lean_ctor_get(v___x_4609_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4609_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4609_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4609_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object* v_body_4626_, lean_object* v_snd_4627_, lean_object* v_name_4628_, lean_object* v_bi_4629_, lean_object* v_type_4630_, lean_object* v_kind_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v_bi_boxed_4637_; uint8_t v_kind_boxed_4638_; lean_object* v_res_4639_; 
v_bi_boxed_4637_ = lean_unbox(v_bi_4629_);
v_kind_boxed_4638_ = lean_unbox(v_kind_4631_);
v_res_4639_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4626_, v_snd_4627_, v_name_4628_, v_bi_boxed_4637_, v_type_4630_, v_kind_boxed_4638_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
return v_res_4639_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0));
v___x_4642_ = l_Lean_stringToMessageData(v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6));
v___x_4651_ = l_Lean_stringToMessageData(v___x_4650_);
return v___x_4651_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8));
v___x_4654_ = l_Lean_stringToMessageData(v___x_4653_);
return v___x_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object* v_mvarId_4655_, lean_object* v_userName_x3f_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v___y_4663_; lean_object* v___y_4664_; uint8_t v___y_4665_; lean_object* v___y_4666_; lean_object* v___y_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4686_; lean_object* v___y_4687_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___y_4694_; lean_object* v___x_4733_; 
lean_inc(v_mvarId_4655_);
v___x_4733_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_4655_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v_fst_4735_; lean_object* v_snd_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4869_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
v_fst_4735_ = lean_ctor_get(v_a_4734_, 0);
v_snd_4736_ = lean_ctor_get(v_a_4734_, 1);
v_isSharedCheck_4869_ = !lean_is_exclusive(v_a_4734_);
if (v_isSharedCheck_4869_ == 0)
{
v___x_4738_ = v_a_4734_;
v_isShared_4739_ = v_isSharedCheck_4869_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_snd_4736_);
lean_inc(v_fst_4735_);
lean_dec(v_a_4734_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4869_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4740_; lean_object* v_a_4741_; lean_object* v___x_4742_; 
v___x_4740_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_4735_, v___y_4658_);
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4740_);
v___x_4742_ = l_Lean_Expr_cleanupAnnotations(v_a_4741_);
if (lean_obj_tag(v___x_4742_) == 7)
{
lean_object* v_binderName_4743_; lean_object* v_binderType_4744_; lean_object* v_body_4745_; uint8_t v_binderInfo_4746_; lean_object* v___x_4747_; 
lean_del_object(v___x_4738_);
v_binderName_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc(v_binderName_4743_);
v_binderType_4744_ = lean_ctor_get(v___x_4742_, 1);
lean_inc_ref_n(v_binderType_4744_, 2);
v_body_4745_ = lean_ctor_get(v___x_4742_, 2);
lean_inc_ref(v_body_4745_);
v_binderInfo_4746_ = lean_ctor_get_uint8(v___x_4742_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_4742_, 3);
v___x_4747_ = l_Lean_Meta_getLevel(v_binderType_4744_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; lean_object* v___x_4749_; lean_object* v_userName_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref_known(v___x_4747_, 1);
lean_inc_ref(v_body_4745_);
lean_inc_ref(v_binderType_4744_);
lean_inc(v_binderName_4743_);
v___x_4749_ = l_Lean_Expr_lam___override(v_binderName_4743_, v_binderType_4744_, v_body_4745_, v_binderInfo_4746_);
if (lean_obj_tag(v_userName_x3f_4656_) == 1)
{
lean_object* v_val_4792_; 
lean_dec(v_binderName_4743_);
v_val_4792_ = lean_ctor_get(v_userName_x3f_4656_, 0);
lean_inc(v_val_4792_);
lean_dec_ref_known(v_userName_x3f_4656_, 1);
v_userName_4751_ = v_val_4792_;
v___y_4752_ = v___y_4657_;
v___y_4753_ = v___y_4658_;
v___y_4754_ = v___y_4659_;
v___y_4755_ = v___y_4660_;
goto v___jp_4750_;
}
else
{
lean_object* v___x_4793_; 
lean_dec(v_userName_x3f_4656_);
v___x_4793_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_4743_, v___y_4657_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4793_, 1);
v_userName_4751_ = v_a_4794_;
v___y_4752_ = v___y_4657_;
v___y_4753_ = v___y_4658_;
v___y_4754_ = v___y_4659_;
v___y_4755_ = v___y_4660_;
goto v___jp_4750_;
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec_ref(v___x_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_body_4745_);
lean_dec_ref(v_binderType_4744_);
lean_dec(v_snd_4736_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_mvarId_4655_);
v_a_4795_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4793_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4793_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
v___jp_4750_:
{
uint8_t v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = 0;
lean_inc_ref(v_binderType_4744_);
v___x_4757_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4745_, v_snd_4736_, v_userName_4751_, v_binderInfo_4746_, v_binderType_4744_, v___x_4756_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec_ref(v___y_4752_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v_snd_4759_; lean_object* v_fst_4760_; lean_object* v_fst_4761_; lean_object* v_snd_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4783_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4757_, 1);
v_snd_4759_ = lean_ctor_get(v_a_4758_, 1);
lean_inc(v_snd_4759_);
v_fst_4760_ = lean_ctor_get(v_a_4758_, 0);
lean_inc(v_fst_4760_);
lean_dec(v_a_4758_);
v_fst_4761_ = lean_ctor_get(v_snd_4759_, 0);
v_snd_4762_ = lean_ctor_get(v_snd_4759_, 1);
v_isSharedCheck_4783_ = !lean_is_exclusive(v_snd_4759_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4764_ = v_snd_4759_;
v_isShared_4765_ = v_isSharedCheck_4783_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_snd_4762_);
lean_inc(v_fst_4761_);
lean_dec(v_snd_4759_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4783_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4769_; 
v___x_4766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5));
v___x_4767_ = lean_box(0);
if (v_isShared_4765_ == 0)
{
lean_ctor_set_tag(v___x_4764_, 1);
lean_ctor_set(v___x_4764_, 1, v___x_4767_);
lean_ctor_set(v___x_4764_, 0, v_a_4748_);
v___x_4769_ = v___x_4764_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4748_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v___x_4767_);
v___x_4769_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4780_; 
v___x_4770_ = l_Lean_mkConst(v___x_4766_, v___x_4769_);
v___x_4771_ = l_Lean_mkApp4(v___x_4770_, v_binderType_4744_, v___x_4749_, v_fst_4760_, v_fst_4761_);
v___x_4772_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4655_, v___x_4771_, v___y_4753_);
lean_dec(v___y_4753_);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4772_);
if (v_isSharedCheck_4780_ == 0)
{
lean_object* v_unused_4781_; 
v_unused_4781_ = lean_ctor_get(v___x_4772_, 0);
lean_dec(v_unused_4781_);
v___x_4774_ = v___x_4772_;
v_isShared_4775_ = v_isSharedCheck_4780_;
goto v_resetjp_4773_;
}
else
{
lean_dec(v___x_4772_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4780_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4776_; lean_object* v___x_4778_; 
v___x_4776_ = l_Lean_Expr_mvarId_x21(v_snd_4762_);
lean_dec(v_snd_4762_);
if (v_isShared_4775_ == 0)
{
lean_ctor_set(v___x_4774_, 0, v___x_4776_);
v___x_4778_ = v___x_4774_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec(v___y_4753_);
lean_dec_ref(v___x_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_binderType_4744_);
lean_dec(v_mvarId_4655_);
v_a_4784_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4757_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4757_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec_ref(v_body_4745_);
lean_dec_ref(v_binderType_4744_);
lean_dec(v_binderName_4743_);
lean_dec(v_snd_4736_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v_a_4803_ = lean_ctor_get(v___x_4747_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4747_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4747_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4747_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v___x_4811_; 
lean_inc_ref(v___x_4742_);
lean_inc(v_mvarId_4655_);
v___x_4811_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4655_, v___x_4742_, v_snd_4736_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4860_; 
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4814_ = v___x_4811_;
v_isShared_4815_ = v_isSharedCheck_4860_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4811_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4860_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
if (lean_obj_tag(v_a_4812_) == 1)
{
lean_object* v_val_4816_; lean_object* v___x_4818_; 
lean_dec_ref(v___x_4742_);
lean_del_object(v___x_4738_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v_val_4816_ = lean_ctor_get(v_a_4812_, 0);
lean_inc(v_val_4816_);
lean_dec_ref_known(v_a_4812_, 1);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v_val_4816_);
v___x_4818_ = v___x_4814_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_val_4816_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
else
{
lean_object* v___x_4820_; 
lean_del_object(v___x_4814_);
lean_dec(v_a_4812_);
lean_inc(v___y_4660_);
lean_inc_ref(v___y_4659_);
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
lean_inc_ref(v___x_4742_);
v___x_4820_ = lean_infer_type(v___x_4742_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v_a_4821_; lean_object* v___x_4822_; 
v_a_4821_ = lean_ctor_get(v___x_4820_, 0);
lean_inc(v_a_4821_);
lean_dec_ref_known(v___x_4820_, 1);
v___x_4822_ = l_Lean_Meta_whnfD(v_a_4821_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; uint8_t v___x_4824_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v___x_4824_ = l_Lean_Expr_isForall(v_a_4823_);
if (v___x_4824_ == 0)
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4829_; 
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v___x_4825_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7);
v___x_4826_ = l_Lean_MessageData_ofExpr(v___x_4742_);
v___x_4827_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9);
if (v_isShared_4739_ == 0)
{
lean_ctor_set_tag(v___x_4738_, 7);
lean_ctor_set(v___x_4738_, 1, v___x_4827_);
lean_ctor_set(v___x_4738_, 0, v___x_4826_);
v___x_4829_ = v___x_4738_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v___x_4827_);
v___x_4829_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
v___x_4830_ = l_Lean_MessageData_ofExpr(v_a_4823_);
v___x_4831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = l_Lean_indentD(v___x_4831_);
v___x_4833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4825_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4833_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4834_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4834_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4834_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
else
{
lean_dec(v_a_4823_);
lean_dec_ref(v___x_4742_);
lean_del_object(v___x_4738_);
v___y_4691_ = v___y_4657_;
v___y_4692_ = v___y_4658_;
v___y_4693_ = v___y_4659_;
v___y_4694_ = v___y_4660_;
goto v___jp_4690_;
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
lean_dec_ref(v___x_4742_);
lean_del_object(v___x_4738_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v_a_4844_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4822_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4822_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_dec_ref(v___x_4742_);
lean_del_object(v___x_4738_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v_a_4852_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4820_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4820_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
lean_dec_ref(v___x_4742_);
lean_del_object(v___x_4738_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v_a_4861_ = lean_ctor_get(v___x_4811_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4811_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4811_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
}
else
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4877_; 
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v_a_4870_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4872_ = v___x_4733_;
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4733_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4877_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4875_; 
if (v_isShared_4873_ == 0)
{
v___x_4875_ = v___x_4872_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_a_4870_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
v___jp_4662_:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = lean_unsigned_to_nat(1u);
v___x_4671_ = l_Lean_Meta_introNCore(v___y_4663_, v___x_4670_, v___y_4669_, v___y_4665_, v___y_4665_, v___y_4668_, v___y_4664_, v___y_4666_, v___y_4667_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v_snd_4673_; lean_object* v___x_4674_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v___x_4671_, 1);
v_snd_4673_ = lean_ctor_get(v_a_4672_, 1);
lean_inc(v_snd_4673_);
lean_dec(v_a_4672_);
v___x_4674_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4673_, v___y_4668_, v___y_4664_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4668_);
return v___x_4674_;
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4682_; 
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4664_);
v_a_4675_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4677_ = v___x_4671_;
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
else
{
lean_inc(v_a_4675_);
lean_dec(v___x_4671_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4682_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4680_; 
if (v_isShared_4678_ == 0)
{
v___x_4680_ = v___x_4677_;
goto v_reusejp_4679_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_a_4675_);
v___x_4680_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4679_;
}
v_reusejp_4679_:
{
return v___x_4680_;
}
}
}
}
v___jp_4683_:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4688_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1);
v___x_4689_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4688_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
return v___x_4689_;
}
v___jp_4690_:
{
lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3));
v___x_4696_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_4695_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; uint8_t v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
lean_inc(v_a_4697_);
lean_dec_ref_known(v___x_4696_, 1);
v___x_4698_ = 0;
v___x_4699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2));
v___x_4700_ = lean_box(0);
v___x_4701_ = l_Lean_MVarId_apply(v_mvarId_4655_, v_a_4697_, v___x_4699_, v___x_4700_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
if (lean_obj_tag(v_a_4702_) == 1)
{
lean_object* v_tail_4703_; 
v_tail_4703_ = lean_ctor_get(v_a_4702_, 1);
if (lean_obj_tag(v_tail_4703_) == 0)
{
if (lean_obj_tag(v_userName_x3f_4656_) == 1)
{
lean_object* v_head_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4713_; 
v_head_4704_ = lean_ctor_get(v_a_4702_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v_a_4702_);
if (v_isSharedCheck_4713_ == 0)
{
lean_object* v_unused_4714_; 
v_unused_4714_ = lean_ctor_get(v_a_4702_, 1);
lean_dec(v_unused_4714_);
v___x_4706_ = v_a_4702_;
v_isShared_4707_ = v_isSharedCheck_4713_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_head_4704_);
lean_dec(v_a_4702_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4713_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v_val_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v_val_4708_ = lean_ctor_get(v_userName_x3f_4656_, 0);
lean_inc(v_val_4708_);
lean_dec_ref_known(v_userName_x3f_4656_, 1);
v___x_4709_ = lean_box(0);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 1, v___x_4709_);
lean_ctor_set(v___x_4706_, 0, v_val_4708_);
v___x_4711_ = v___x_4706_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_val_4708_);
lean_ctor_set(v_reuseFailAlloc_4712_, 1, v___x_4709_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
v___y_4663_ = v_head_4704_;
v___y_4664_ = v___y_4692_;
v___y_4665_ = v___x_4698_;
v___y_4666_ = v___y_4693_;
v___y_4667_ = v___y_4694_;
v___y_4668_ = v___y_4691_;
v___y_4669_ = v___x_4711_;
goto v___jp_4662_;
}
}
}
else
{
lean_object* v_head_4715_; lean_object* v___x_4716_; 
lean_dec(v_userName_x3f_4656_);
v_head_4715_ = lean_ctor_get(v_a_4702_, 0);
lean_inc(v_head_4715_);
lean_dec_ref_known(v_a_4702_, 2);
v___x_4716_ = lean_box(0);
v___y_4663_ = v_head_4715_;
v___y_4664_ = v___y_4692_;
v___y_4665_ = v___x_4698_;
v___y_4666_ = v___y_4693_;
v___y_4667_ = v___y_4694_;
v___y_4668_ = v___y_4691_;
v___y_4669_ = v___x_4716_;
goto v___jp_4662_;
}
}
else
{
lean_dec_ref_known(v_a_4702_, 2);
lean_dec(v_userName_x3f_4656_);
v___y_4684_ = v___y_4691_;
v___y_4685_ = v___y_4692_;
v___y_4686_ = v___y_4693_;
v___y_4687_ = v___y_4694_;
goto v___jp_4683_;
}
}
else
{
lean_dec(v_a_4702_);
lean_dec(v_userName_x3f_4656_);
v___y_4684_ = v___y_4691_;
v___y_4685_ = v___y_4692_;
v___y_4686_ = v___y_4693_;
v___y_4687_ = v___y_4694_;
goto v___jp_4683_;
}
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v_userName_x3f_4656_);
v_a_4717_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4701_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4701_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
else
{
lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4732_; 
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v_userName_x3f_4656_);
lean_dec(v_mvarId_4655_);
v_a_4725_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4732_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4732_ == 0)
{
v___x_4727_ = v___x_4696_;
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4696_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4732_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4730_; 
if (v_isShared_4728_ == 0)
{
v___x_4730_ = v___x_4727_;
goto v_reusejp_4729_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_a_4725_);
v___x_4730_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4729_;
}
v_reusejp_4729_:
{
return v___x_4730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed(lean_object* v_mvarId_4878_, lean_object* v_userName_x3f_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(v_mvarId_4878_, v_userName_x3f_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(lean_object* v_mvarId_4886_, lean_object* v_userName_x3f_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v___f_4893_; lean_object* v___x_4894_; 
lean_inc(v_mvarId_4886_);
v___f_4893_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4893_, 0, v_mvarId_4886_);
lean_closure_set(v___f_4893_, 1, v_userName_x3f_4887_);
v___x_4894_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_4886_, v___f_4893_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___boxed(lean_object* v_mvarId_4895_, lean_object* v_userName_x3f_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_mvarId_4895_, v_userName_x3f_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec(v_a_4898_);
lean_dec_ref(v_a_4897_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(lean_object* v_userName_x3f_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v___x_4912_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_a_4911_, v_userName_x3f_4903_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = lean_box(0);
v___x_4915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4915_, 0, v_a_4913_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
v___x_4916_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4915_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_);
return v___x_4916_;
}
else
{
lean_object* v_a_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
v_a_4917_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4919_ = v___x_4912_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_inc(v_a_4917_);
lean_dec(v___x_4912_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec(v_userName_x3f_4903_);
v_a_4925_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4910_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4910_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg___boxed(lean_object* v_userName_x3f_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_a_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v_a_4934_);
return v_res_4940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(lean_object* v_userName_x3f_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v___x_4951_; 
v___x_4951_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_4941_, v_a_4943_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___boxed(lean_object* v_userName_x3f_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(v_userName_x3f_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
lean_dec_ref(v_a_4953_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(lean_object* v_as_4970_, size_t v_sz_4971_, size_t v_i_4972_, lean_object* v_b_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
uint8_t v___x_4980_; 
v___x_4980_ = lean_usize_dec_lt(v_i_4972_, v_sz_4971_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; 
v___x_4981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4981_, 0, v_b_4973_);
return v___x_4981_;
}
else
{
lean_object* v___x_4982_; lean_object* v_a_4983_; lean_object* v___y_4985_; lean_object* v___x_5008_; uint8_t v___x_5009_; 
v___x_4982_ = lean_box(0);
v_a_4983_ = lean_array_uget_borrowed(v_as_4970_, v_i_4972_);
v___x_5008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1));
lean_inc(v_a_4983_);
v___x_5009_ = l_Lean_Syntax_isOfKind(v_a_4983_, v___x_5008_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
v___x_5010_ = lean_box(0);
v___y_4985_ = v___x_5010_;
goto v___jp_4984_;
}
else
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; uint8_t v___x_5014_; 
v___x_5011_ = lean_unsigned_to_nat(0u);
v___x_5012_ = l_Lean_Syntax_getArg(v_a_4983_, v___x_5011_);
v___x_5013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3));
lean_inc(v___x_5012_);
v___x_5014_ = l_Lean_Syntax_isOfKind(v___x_5012_, v___x_5013_);
if (v___x_5014_ == 0)
{
lean_object* v___x_5015_; 
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v___y_4985_ = v___x_5015_;
goto v___jp_4984_;
}
else
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = l_Lean_TSyntax_getId(v___x_5012_);
lean_dec(v___x_5012_);
v___x_5017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
v___y_4985_ = v___x_5017_;
goto v___jp_4984_;
}
}
v___jp_4984_:
{
lean_object* v_fileName_4986_; lean_object* v_fileMap_4987_; lean_object* v_options_4988_; lean_object* v_currRecDepth_4989_; lean_object* v_maxRecDepth_4990_; lean_object* v_ref_4991_; lean_object* v_currNamespace_4992_; lean_object* v_openDecls_4993_; lean_object* v_initHeartbeats_4994_; lean_object* v_maxHeartbeats_4995_; lean_object* v_quotContext_4996_; lean_object* v_currMacroScope_4997_; uint8_t v_diag_4998_; lean_object* v_cancelTk_x3f_4999_; uint8_t v_suppressElabErrors_5000_; lean_object* v_inheritedTraceOptions_5001_; lean_object* v_ref_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v_fileName_4986_ = lean_ctor_get(v___y_4977_, 0);
v_fileMap_4987_ = lean_ctor_get(v___y_4977_, 1);
v_options_4988_ = lean_ctor_get(v___y_4977_, 2);
v_currRecDepth_4989_ = lean_ctor_get(v___y_4977_, 3);
v_maxRecDepth_4990_ = lean_ctor_get(v___y_4977_, 4);
v_ref_4991_ = lean_ctor_get(v___y_4977_, 5);
v_currNamespace_4992_ = lean_ctor_get(v___y_4977_, 6);
v_openDecls_4993_ = lean_ctor_get(v___y_4977_, 7);
v_initHeartbeats_4994_ = lean_ctor_get(v___y_4977_, 8);
v_maxHeartbeats_4995_ = lean_ctor_get(v___y_4977_, 9);
v_quotContext_4996_ = lean_ctor_get(v___y_4977_, 10);
v_currMacroScope_4997_ = lean_ctor_get(v___y_4977_, 11);
v_diag_4998_ = lean_ctor_get_uint8(v___y_4977_, sizeof(void*)*14);
v_cancelTk_x3f_4999_ = lean_ctor_get(v___y_4977_, 12);
v_suppressElabErrors_5000_ = lean_ctor_get_uint8(v___y_4977_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5001_ = lean_ctor_get(v___y_4977_, 13);
v_ref_5002_ = l_Lean_replaceRef(v_a_4983_, v_ref_4991_);
lean_inc_ref(v_inheritedTraceOptions_5001_);
lean_inc(v_cancelTk_x3f_4999_);
lean_inc(v_currMacroScope_4997_);
lean_inc(v_quotContext_4996_);
lean_inc(v_maxHeartbeats_4995_);
lean_inc(v_initHeartbeats_4994_);
lean_inc(v_openDecls_4993_);
lean_inc(v_currNamespace_4992_);
lean_inc(v_maxRecDepth_4990_);
lean_inc(v_currRecDepth_4989_);
lean_inc_ref(v_options_4988_);
lean_inc_ref(v_fileMap_4987_);
lean_inc_ref(v_fileName_4986_);
v___x_5003_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5003_, 0, v_fileName_4986_);
lean_ctor_set(v___x_5003_, 1, v_fileMap_4987_);
lean_ctor_set(v___x_5003_, 2, v_options_4988_);
lean_ctor_set(v___x_5003_, 3, v_currRecDepth_4989_);
lean_ctor_set(v___x_5003_, 4, v_maxRecDepth_4990_);
lean_ctor_set(v___x_5003_, 5, v_ref_5002_);
lean_ctor_set(v___x_5003_, 6, v_currNamespace_4992_);
lean_ctor_set(v___x_5003_, 7, v_openDecls_4993_);
lean_ctor_set(v___x_5003_, 8, v_initHeartbeats_4994_);
lean_ctor_set(v___x_5003_, 9, v_maxHeartbeats_4995_);
lean_ctor_set(v___x_5003_, 10, v_quotContext_4996_);
lean_ctor_set(v___x_5003_, 11, v_currMacroScope_4997_);
lean_ctor_set(v___x_5003_, 12, v_cancelTk_x3f_4999_);
lean_ctor_set(v___x_5003_, 13, v_inheritedTraceOptions_5001_);
lean_ctor_set_uint8(v___x_5003_, sizeof(void*)*14, v_diag_4998_);
lean_ctor_set_uint8(v___x_5003_, sizeof(void*)*14 + 1, v_suppressElabErrors_5000_);
v___x_5004_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___y_4985_, v___y_4974_, v___y_4975_, v___y_4976_, v___x_5003_, v___y_4978_);
lean_dec_ref_known(v___x_5003_, 14);
if (lean_obj_tag(v___x_5004_) == 0)
{
size_t v___x_5005_; size_t v___x_5006_; 
lean_dec_ref_known(v___x_5004_, 1);
v___x_5005_ = ((size_t)1ULL);
v___x_5006_ = lean_usize_add(v_i_4972_, v___x_5005_);
v_i_4972_ = v___x_5006_;
v_b_4973_ = v___x_4982_;
goto _start;
}
else
{
return v___x_5004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object* v_as_5018_, lean_object* v_sz_5019_, lean_object* v_i_5020_, lean_object* v_b_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
size_t v_sz_boxed_5028_; size_t v_i_boxed_5029_; lean_object* v_res_5030_; 
v_sz_boxed_5028_ = lean_unbox_usize(v_sz_5019_);
lean_dec(v_sz_5019_);
v_i_boxed_5029_ = lean_unbox_usize(v_i_5020_);
lean_dec(v_i_5020_);
v_res_5030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5018_, v_sz_boxed_5028_, v_i_boxed_5029_, v_b_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v_as_5018_);
return v_res_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object* v_stx_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v_ids_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; 
v___x_5041_ = lean_unsigned_to_nat(1u);
v___x_5042_ = l_Lean_Syntax_getArg(v_stx_5031_, v___x_5041_);
v_ids_5043_ = l_Lean_Syntax_getArgs(v___x_5042_);
lean_dec(v___x_5042_);
v___x_5044_ = lean_array_get_size(v_ids_5043_);
v___x_5045_ = lean_unsigned_to_nat(0u);
v___x_5046_ = lean_nat_dec_eq(v___x_5044_, v___x_5045_);
if (v___x_5046_ == 0)
{
lean_object* v___x_5047_; size_t v_sz_5048_; size_t v___x_5049_; lean_object* v___x_5050_; 
v___x_5047_ = lean_box(0);
v_sz_5048_ = lean_array_size(v_ids_5043_);
v___x_5049_ = ((size_t)0ULL);
v___x_5050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_ids_5043_, v_sz_5048_, v___x_5049_, v___x_5047_, v_a_5033_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_);
lean_dec_ref(v_ids_5043_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5057_ == 0)
{
lean_object* v_unused_5058_; 
v_unused_5058_ = lean_ctor_get(v___x_5050_, 0);
lean_dec(v_unused_5058_);
v___x_5052_ = v___x_5050_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_dec(v___x_5050_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5047_);
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5047_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
else
{
return v___x_5050_;
}
}
else
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_dec_ref(v_ids_5043_);
v___x_5059_ = lean_box(0);
v___x_5060_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___x_5059_, v_a_5033_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_);
return v___x_5060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object* v_stx_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l_Lean_Elab_Tactic_Conv_evalExt(v_stx_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_, v_a_5068_, v_a_5069_);
lean_dec(v_a_5069_);
lean_dec_ref(v_a_5068_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
lean_dec(v_stx_5061_);
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object* v_as_5072_, size_t v_sz_5073_, size_t v_i_5074_, lean_object* v_b_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v___x_5085_; 
v___x_5085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5072_, v_sz_5073_, v_i_5074_, v_b_5075_, v___y_5077_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object* v_as_5086_, lean_object* v_sz_5087_, lean_object* v_i_5088_, lean_object* v_b_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
size_t v_sz_boxed_5099_; size_t v_i_boxed_5100_; lean_object* v_res_5101_; 
v_sz_boxed_5099_ = lean_unbox_usize(v_sz_5087_);
lean_dec(v_sz_5087_);
v_i_boxed_5100_ = lean_unbox_usize(v_i_5088_);
lean_dec(v_i_5088_);
v_res_5101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(v_as_5086_, v_sz_boxed_5099_, v_i_boxed_5100_, v_b_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v___y_5091_);
lean_dec_ref(v___y_5090_);
lean_dec_ref(v_as_5086_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1(){
_start:
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; 
v___x_5116_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0));
v___x_5118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExt___boxed), 10, 0);
v___x_5120_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5116_, v___x_5117_, v___x_5118_, v___x_5119_);
return v___x_5120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object* v_a_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3(){
_start:
{
lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5150_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6));
v___x_5151_ = l_Lean_addBuiltinDeclarationRanges(v___x_5149_, v___x_5150_);
return v___x_5151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object* v_a_5152_){
_start:
{
lean_object* v_res_5153_; 
v_res_5153_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
return v_res_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object* v_a_5154_, lean_object* v_trees_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
lean_object* v___x_5165_; 
lean_inc(v___y_5163_);
lean_inc_ref(v___y_5162_);
lean_inc(v___y_5161_);
lean_inc_ref(v___y_5160_);
lean_inc(v___y_5159_);
lean_inc_ref(v___y_5158_);
lean_inc(v___y_5157_);
lean_inc_ref(v___y_5156_);
v___x_5165_ = lean_apply_9(v_a_5154_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, lean_box(0));
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; lean_object* v___x_5168_; uint8_t v_isShared_5169_; uint8_t v_isSharedCheck_5174_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5168_ = v___x_5165_;
v_isShared_5169_ = v_isSharedCheck_5174_;
goto v_resetjp_5167_;
}
else
{
lean_inc(v_a_5166_);
lean_dec(v___x_5165_);
v___x_5168_ = lean_box(0);
v_isShared_5169_ = v_isSharedCheck_5174_;
goto v_resetjp_5167_;
}
v_resetjp_5167_:
{
lean_object* v___x_5170_; lean_object* v___x_5172_; 
v___x_5170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5170_, 0, v_a_5166_);
lean_ctor_set(v___x_5170_, 1, v_trees_5155_);
if (v_isShared_5169_ == 0)
{
lean_ctor_set(v___x_5168_, 0, v___x_5170_);
v___x_5172_ = v___x_5168_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5170_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
lean_dec_ref(v_trees_5155_);
v_a_5175_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5165_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5165_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object* v_a_5183_, lean_object* v_trees_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v_res_5194_; 
v_res_5194_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(v_a_5183_, v_trees_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
lean_dec(v___y_5192_);
lean_dec_ref(v___y_5191_);
lean_dec(v___y_5190_);
lean_dec_ref(v___y_5189_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
return v_res_5194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object* v___x_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_){
_start:
{
lean_object* v___x_5205_; 
v___x_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5195_);
return v___x_5205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object* v___x_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(v___x_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(lean_object* v_a_5217_, lean_object* v_trees_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_){
_start:
{
lean_object* v___x_5228_; 
lean_inc(v___y_5226_);
lean_inc_ref(v___y_5225_);
lean_inc(v___y_5224_);
lean_inc_ref(v___y_5223_);
lean_inc(v___y_5222_);
lean_inc_ref(v___y_5221_);
lean_inc(v___y_5220_);
lean_inc_ref(v___y_5219_);
v___x_5228_ = lean_apply_9(v_a_5217_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, lean_box(0));
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v___x_5231_; uint8_t v_isShared_5232_; uint8_t v_isSharedCheck_5237_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5237_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5237_ == 0)
{
v___x_5231_ = v___x_5228_;
v_isShared_5232_ = v_isSharedCheck_5237_;
goto v_resetjp_5230_;
}
else
{
lean_inc(v_a_5229_);
lean_dec(v___x_5228_);
v___x_5231_ = lean_box(0);
v_isShared_5232_ = v_isSharedCheck_5237_;
goto v_resetjp_5230_;
}
v_resetjp_5230_:
{
lean_object* v___x_5233_; lean_object* v___x_5235_; 
v___x_5233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5233_, 0, v_a_5229_);
lean_ctor_set(v___x_5233_, 1, v_trees_5218_);
if (v_isShared_5232_ == 0)
{
lean_ctor_set(v___x_5231_, 0, v___x_5233_);
v___x_5235_ = v___x_5231_;
goto v_reusejp_5234_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___x_5233_);
v___x_5235_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5234_;
}
v_reusejp_5234_:
{
return v___x_5235_;
}
}
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
lean_dec_ref(v_trees_5218_);
v_a_5238_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5228_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5228_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object* v_a_5246_, lean_object* v_trees_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(v_a_5246_, v_trees_5247_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(uint8_t v___x_5258_, lean_object* v___x_5259_, lean_object* v___x_5260_, lean_object* v___x_5261_, lean_object* v___x_5262_, lean_object* v___x_5263_, lean_object* v___x_5264_, lean_object* v___x_5265_, lean_object* v___x_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
if (v___x_5258_ == 0)
{
lean_object* v___x_5276_; 
lean_dec_ref(v___y_5273_);
lean_dec(v___x_5266_);
lean_dec_ref(v___x_5265_);
lean_dec_ref(v___x_5264_);
lean_dec_ref(v___x_5263_);
lean_dec_ref(v___x_5262_);
v___x_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5259_);
return v___x_5276_;
}
else
{
lean_object* v_fileName_5277_; lean_object* v_fileMap_5278_; lean_object* v_options_5279_; lean_object* v_currRecDepth_5280_; lean_object* v_maxRecDepth_5281_; lean_object* v_ref_5282_; lean_object* v_currNamespace_5283_; lean_object* v_openDecls_5284_; lean_object* v_initHeartbeats_5285_; lean_object* v_maxHeartbeats_5286_; lean_object* v_quotContext_5287_; lean_object* v_currMacroScope_5288_; uint8_t v_diag_5289_; lean_object* v_cancelTk_x3f_5290_; uint8_t v_suppressElabErrors_5291_; lean_object* v_inheritedTraceOptions_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5322_; 
v_fileName_5277_ = lean_ctor_get(v___y_5273_, 0);
v_fileMap_5278_ = lean_ctor_get(v___y_5273_, 1);
v_options_5279_ = lean_ctor_get(v___y_5273_, 2);
v_currRecDepth_5280_ = lean_ctor_get(v___y_5273_, 3);
v_maxRecDepth_5281_ = lean_ctor_get(v___y_5273_, 4);
v_ref_5282_ = lean_ctor_get(v___y_5273_, 5);
v_currNamespace_5283_ = lean_ctor_get(v___y_5273_, 6);
v_openDecls_5284_ = lean_ctor_get(v___y_5273_, 7);
v_initHeartbeats_5285_ = lean_ctor_get(v___y_5273_, 8);
v_maxHeartbeats_5286_ = lean_ctor_get(v___y_5273_, 9);
v_quotContext_5287_ = lean_ctor_get(v___y_5273_, 10);
v_currMacroScope_5288_ = lean_ctor_get(v___y_5273_, 11);
v_diag_5289_ = lean_ctor_get_uint8(v___y_5273_, sizeof(void*)*14);
v_cancelTk_x3f_5290_ = lean_ctor_get(v___y_5273_, 12);
v_suppressElabErrors_5291_ = lean_ctor_get_uint8(v___y_5273_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5292_ = lean_ctor_get(v___y_5273_, 13);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___y_5273_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5294_ = v___y_5273_;
v_isShared_5295_ = v_isSharedCheck_5322_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_inheritedTraceOptions_5292_);
lean_inc(v_cancelTk_x3f_5290_);
lean_inc(v_currMacroScope_5288_);
lean_inc(v_quotContext_5287_);
lean_inc(v_maxHeartbeats_5286_);
lean_inc(v_initHeartbeats_5285_);
lean_inc(v_openDecls_5284_);
lean_inc(v_currNamespace_5283_);
lean_inc(v_ref_5282_);
lean_inc(v_maxRecDepth_5281_);
lean_inc(v_currRecDepth_5280_);
lean_inc(v_options_5279_);
lean_inc(v_fileMap_5278_);
lean_inc(v_fileName_5277_);
lean_dec(v___y_5273_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5322_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v_ref_5296_; lean_object* v___x_5298_; 
v_ref_5296_ = l_Lean_replaceRef(v___x_5260_, v_ref_5282_);
lean_dec(v_ref_5282_);
lean_inc(v_ref_5296_);
if (v_isShared_5295_ == 0)
{
lean_ctor_set(v___x_5294_, 5, v_ref_5296_);
v___x_5298_ = v___x_5294_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_fileName_5277_);
lean_ctor_set(v_reuseFailAlloc_5321_, 1, v_fileMap_5278_);
lean_ctor_set(v_reuseFailAlloc_5321_, 2, v_options_5279_);
lean_ctor_set(v_reuseFailAlloc_5321_, 3, v_currRecDepth_5280_);
lean_ctor_set(v_reuseFailAlloc_5321_, 4, v_maxRecDepth_5281_);
lean_ctor_set(v_reuseFailAlloc_5321_, 5, v_ref_5296_);
lean_ctor_set(v_reuseFailAlloc_5321_, 6, v_currNamespace_5283_);
lean_ctor_set(v_reuseFailAlloc_5321_, 7, v_openDecls_5284_);
lean_ctor_set(v_reuseFailAlloc_5321_, 8, v_initHeartbeats_5285_);
lean_ctor_set(v_reuseFailAlloc_5321_, 9, v_maxHeartbeats_5286_);
lean_ctor_set(v_reuseFailAlloc_5321_, 10, v_quotContext_5287_);
lean_ctor_set(v_reuseFailAlloc_5321_, 11, v_currMacroScope_5288_);
lean_ctor_set(v_reuseFailAlloc_5321_, 12, v_cancelTk_x3f_5290_);
lean_ctor_set(v_reuseFailAlloc_5321_, 13, v_inheritedTraceOptions_5292_);
lean_ctor_set_uint8(v_reuseFailAlloc_5321_, sizeof(void*)*14, v_diag_5289_);
lean_ctor_set_uint8(v_reuseFailAlloc_5321_, sizeof(void*)*14 + 1, v_suppressElabErrors_5291_);
v___x_5298_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; uint8_t v___x_5302_; 
v___x_5299_ = l_Lean_Syntax_getArg(v___x_5260_, v___x_5261_);
v___x_5300_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__4));
lean_inc_ref(v___x_5265_);
lean_inc_ref(v___x_5264_);
lean_inc_ref(v___x_5263_);
lean_inc_ref(v___x_5262_);
v___x_5301_ = l_Lean_Name_mkStr5(v___x_5262_, v___x_5263_, v___x_5264_, v___x_5265_, v___x_5300_);
lean_inc(v___x_5299_);
v___x_5302_ = l_Lean_Syntax_isOfKind(v___x_5299_, v___x_5301_);
lean_dec(v___x_5301_);
if (v___x_5302_ == 0)
{
lean_object* v___x_5303_; lean_object* v___x_5304_; uint8_t v___x_5305_; 
v___x_5303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0));
lean_inc_ref(v___x_5262_);
v___x_5304_ = l_Lean_Name_mkStr2(v___x_5262_, v___x_5303_);
lean_inc(v___x_5299_);
v___x_5305_ = l_Lean_Syntax_isOfKind(v___x_5299_, v___x_5304_);
lean_dec(v___x_5304_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; 
lean_dec(v___x_5299_);
lean_dec_ref(v___x_5298_);
lean_dec(v_ref_5296_);
lean_dec(v___x_5266_);
lean_dec_ref(v___x_5265_);
lean_dec_ref(v___x_5264_);
lean_dec_ref(v___x_5263_);
lean_dec_ref(v___x_5262_);
v___x_5306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5259_);
return v___x_5306_;
}
else
{
lean_object* v___x_5307_; lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5307_ = l_Lean_SourceInfo_fromRef(v_ref_5296_, v___x_5302_);
lean_dec(v_ref_5296_);
v___x_5308_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_5309_ = l_Lean_Name_mkStr5(v___x_5262_, v___x_5263_, v___x_5264_, v___x_5265_, v___x_5308_);
lean_inc_n(v___x_5307_, 2);
v___x_5310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5307_);
lean_ctor_set(v___x_5310_, 1, v___x_5308_);
v___x_5311_ = l_Lean_Syntax_node1(v___x_5307_, v___x_5266_, v___x_5299_);
v___x_5312_ = l_Lean_Syntax_node2(v___x_5307_, v___x_5309_, v___x_5310_, v___x_5311_);
v___x_5313_ = l_Lean_Elab_Tactic_evalTactic(v___x_5312_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___x_5298_, v___y_5274_);
lean_dec_ref(v___x_5298_);
return v___x_5313_;
}
}
else
{
uint8_t v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
lean_dec(v___x_5266_);
v___x_5314_ = 0;
v___x_5315_ = l_Lean_SourceInfo_fromRef(v_ref_5296_, v___x_5314_);
lean_dec(v_ref_5296_);
v___x_5316_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_5317_ = l_Lean_Name_mkStr5(v___x_5262_, v___x_5263_, v___x_5264_, v___x_5265_, v___x_5316_);
lean_inc(v___x_5315_);
v___x_5318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5315_);
lean_ctor_set(v___x_5318_, 1, v___x_5316_);
v___x_5319_ = l_Lean_Syntax_node2(v___x_5315_, v___x_5317_, v___x_5318_, v___x_5299_);
v___x_5320_ = l_Lean_Elab_Tactic_evalTactic(v___x_5319_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___x_5298_, v___y_5274_);
lean_dec_ref(v___x_5298_);
return v___x_5320_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5323_ = _args[0];
lean_object* v___x_5324_ = _args[1];
lean_object* v___x_5325_ = _args[2];
lean_object* v___x_5326_ = _args[3];
lean_object* v___x_5327_ = _args[4];
lean_object* v___x_5328_ = _args[5];
lean_object* v___x_5329_ = _args[6];
lean_object* v___x_5330_ = _args[7];
lean_object* v___x_5331_ = _args[8];
lean_object* v___y_5332_ = _args[9];
lean_object* v___y_5333_ = _args[10];
lean_object* v___y_5334_ = _args[11];
lean_object* v___y_5335_ = _args[12];
lean_object* v___y_5336_ = _args[13];
lean_object* v___y_5337_ = _args[14];
lean_object* v___y_5338_ = _args[15];
lean_object* v___y_5339_ = _args[16];
lean_object* v___y_5340_ = _args[17];
_start:
{
uint8_t v___x_16237__boxed_5341_; lean_object* v_res_5342_; 
v___x_16237__boxed_5341_ = lean_unbox(v___x_5323_);
v_res_5342_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(v___x_16237__boxed_5341_, v___x_5324_, v___x_5325_, v___x_5326_, v___x_5327_, v___x_5328_, v___x_5329_, v___x_5330_, v___x_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
lean_dec(v___y_5339_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___x_5326_);
lean_dec(v___x_5325_);
return v_res_5342_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; 
v___x_5343_ = lean_unsigned_to_nat(32u);
v___x_5344_ = lean_mk_empty_array_with_capacity(v___x_5343_);
v___x_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5344_);
return v___x_5345_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; 
v___x_5346_ = ((size_t)5ULL);
v___x_5347_ = lean_unsigned_to_nat(0u);
v___x_5348_ = lean_unsigned_to_nat(32u);
v___x_5349_ = lean_mk_empty_array_with_capacity(v___x_5348_);
v___x_5350_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0);
v___x_5351_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5351_, 0, v___x_5350_);
lean_ctor_set(v___x_5351_, 1, v___x_5349_);
lean_ctor_set(v___x_5351_, 2, v___x_5347_);
lean_ctor_set(v___x_5351_, 3, v___x_5347_);
lean_ctor_set_usize(v___x_5351_, 4, v___x_5346_);
return v___x_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object* v___y_5352_){
_start:
{
lean_object* v___x_5354_; lean_object* v_infoState_5355_; lean_object* v_trees_5356_; lean_object* v___x_5357_; lean_object* v_infoState_5358_; lean_object* v_env_5359_; lean_object* v_nextMacroScope_5360_; lean_object* v_ngen_5361_; lean_object* v_auxDeclNGen_5362_; lean_object* v_traceState_5363_; lean_object* v_cache_5364_; lean_object* v_messages_5365_; lean_object* v_snapshotTasks_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5387_; 
v___x_5354_ = lean_st_ref_get(v___y_5352_);
v_infoState_5355_ = lean_ctor_get(v___x_5354_, 7);
lean_inc_ref(v_infoState_5355_);
lean_dec(v___x_5354_);
v_trees_5356_ = lean_ctor_get(v_infoState_5355_, 2);
lean_inc_ref(v_trees_5356_);
lean_dec_ref(v_infoState_5355_);
v___x_5357_ = lean_st_ref_take(v___y_5352_);
v_infoState_5358_ = lean_ctor_get(v___x_5357_, 7);
v_env_5359_ = lean_ctor_get(v___x_5357_, 0);
v_nextMacroScope_5360_ = lean_ctor_get(v___x_5357_, 1);
v_ngen_5361_ = lean_ctor_get(v___x_5357_, 2);
v_auxDeclNGen_5362_ = lean_ctor_get(v___x_5357_, 3);
v_traceState_5363_ = lean_ctor_get(v___x_5357_, 4);
v_cache_5364_ = lean_ctor_get(v___x_5357_, 5);
v_messages_5365_ = lean_ctor_get(v___x_5357_, 6);
v_snapshotTasks_5366_ = lean_ctor_get(v___x_5357_, 8);
v_isSharedCheck_5387_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5387_ == 0)
{
v___x_5368_ = v___x_5357_;
v_isShared_5369_ = v_isSharedCheck_5387_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_snapshotTasks_5366_);
lean_inc(v_infoState_5358_);
lean_inc(v_messages_5365_);
lean_inc(v_cache_5364_);
lean_inc(v_traceState_5363_);
lean_inc(v_auxDeclNGen_5362_);
lean_inc(v_ngen_5361_);
lean_inc(v_nextMacroScope_5360_);
lean_inc(v_env_5359_);
lean_dec(v___x_5357_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5387_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
uint8_t v_enabled_5370_; lean_object* v_assignment_5371_; lean_object* v_lazyAssignment_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5385_; 
v_enabled_5370_ = lean_ctor_get_uint8(v_infoState_5358_, sizeof(void*)*3);
v_assignment_5371_ = lean_ctor_get(v_infoState_5358_, 0);
v_lazyAssignment_5372_ = lean_ctor_get(v_infoState_5358_, 1);
v_isSharedCheck_5385_ = !lean_is_exclusive(v_infoState_5358_);
if (v_isSharedCheck_5385_ == 0)
{
lean_object* v_unused_5386_; 
v_unused_5386_ = lean_ctor_get(v_infoState_5358_, 2);
lean_dec(v_unused_5386_);
v___x_5374_ = v_infoState_5358_;
v_isShared_5375_ = v_isSharedCheck_5385_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_lazyAssignment_5372_);
lean_inc(v_assignment_5371_);
lean_dec(v_infoState_5358_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5385_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v___x_5376_; lean_object* v___x_5378_; 
v___x_5376_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 2, v___x_5376_);
v___x_5378_ = v___x_5374_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_assignment_5371_);
lean_ctor_set(v_reuseFailAlloc_5384_, 1, v_lazyAssignment_5372_);
lean_ctor_set(v_reuseFailAlloc_5384_, 2, v___x_5376_);
lean_ctor_set_uint8(v_reuseFailAlloc_5384_, sizeof(void*)*3, v_enabled_5370_);
v___x_5378_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
lean_object* v___x_5380_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 7, v___x_5378_);
v___x_5380_ = v___x_5368_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_env_5359_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v_nextMacroScope_5360_);
lean_ctor_set(v_reuseFailAlloc_5383_, 2, v_ngen_5361_);
lean_ctor_set(v_reuseFailAlloc_5383_, 3, v_auxDeclNGen_5362_);
lean_ctor_set(v_reuseFailAlloc_5383_, 4, v_traceState_5363_);
lean_ctor_set(v_reuseFailAlloc_5383_, 5, v_cache_5364_);
lean_ctor_set(v_reuseFailAlloc_5383_, 6, v_messages_5365_);
lean_ctor_set(v_reuseFailAlloc_5383_, 7, v___x_5378_);
lean_ctor_set(v_reuseFailAlloc_5383_, 8, v_snapshotTasks_5366_);
v___x_5380_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; 
v___x_5381_ = lean_st_ref_set(v___y_5352_, v___x_5380_);
v___x_5382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5382_, 0, v_trees_5356_);
return v___x_5382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5388_);
lean_dec(v___y_5388_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object* v___y_5391_, lean_object* v_mkInfoTree_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v_a_5400_, lean_object* v_a_x3f_5401_){
_start:
{
lean_object* v___x_5403_; lean_object* v_infoState_5404_; lean_object* v_trees_5405_; lean_object* v___x_5406_; 
v___x_5403_ = lean_st_ref_get(v___y_5391_);
v_infoState_5404_ = lean_ctor_get(v___x_5403_, 7);
lean_inc_ref(v_infoState_5404_);
lean_dec(v___x_5403_);
v_trees_5405_ = lean_ctor_get(v_infoState_5404_, 2);
lean_inc_ref(v_trees_5405_);
lean_dec_ref(v_infoState_5404_);
lean_inc(v___y_5391_);
lean_inc_ref(v___y_5399_);
lean_inc(v___y_5398_);
lean_inc_ref(v___y_5397_);
lean_inc(v___y_5396_);
lean_inc_ref(v___y_5395_);
lean_inc(v___y_5394_);
lean_inc_ref(v___y_5393_);
v___x_5406_ = lean_apply_10(v_mkInfoTree_5392_, v_trees_5405_, v___y_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5391_, lean_box(0));
if (lean_obj_tag(v___x_5406_) == 0)
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5445_; 
v_a_5407_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5409_ = v___x_5406_;
v_isShared_5410_ = v_isSharedCheck_5445_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5406_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5445_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5411_; lean_object* v_infoState_5412_; lean_object* v_env_5413_; lean_object* v_nextMacroScope_5414_; lean_object* v_ngen_5415_; lean_object* v_auxDeclNGen_5416_; lean_object* v_traceState_5417_; lean_object* v_cache_5418_; lean_object* v_messages_5419_; lean_object* v_snapshotTasks_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5444_; 
v___x_5411_ = lean_st_ref_take(v___y_5391_);
v_infoState_5412_ = lean_ctor_get(v___x_5411_, 7);
v_env_5413_ = lean_ctor_get(v___x_5411_, 0);
v_nextMacroScope_5414_ = lean_ctor_get(v___x_5411_, 1);
v_ngen_5415_ = lean_ctor_get(v___x_5411_, 2);
v_auxDeclNGen_5416_ = lean_ctor_get(v___x_5411_, 3);
v_traceState_5417_ = lean_ctor_get(v___x_5411_, 4);
v_cache_5418_ = lean_ctor_get(v___x_5411_, 5);
v_messages_5419_ = lean_ctor_get(v___x_5411_, 6);
v_snapshotTasks_5420_ = lean_ctor_get(v___x_5411_, 8);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5422_ = v___x_5411_;
v_isShared_5423_ = v_isSharedCheck_5444_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_snapshotTasks_5420_);
lean_inc(v_infoState_5412_);
lean_inc(v_messages_5419_);
lean_inc(v_cache_5418_);
lean_inc(v_traceState_5417_);
lean_inc(v_auxDeclNGen_5416_);
lean_inc(v_ngen_5415_);
lean_inc(v_nextMacroScope_5414_);
lean_inc(v_env_5413_);
lean_dec(v___x_5411_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5444_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
uint8_t v_enabled_5424_; lean_object* v_assignment_5425_; lean_object* v_lazyAssignment_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5442_; 
v_enabled_5424_ = lean_ctor_get_uint8(v_infoState_5412_, sizeof(void*)*3);
v_assignment_5425_ = lean_ctor_get(v_infoState_5412_, 0);
v_lazyAssignment_5426_ = lean_ctor_get(v_infoState_5412_, 1);
v_isSharedCheck_5442_ = !lean_is_exclusive(v_infoState_5412_);
if (v_isSharedCheck_5442_ == 0)
{
lean_object* v_unused_5443_; 
v_unused_5443_ = lean_ctor_get(v_infoState_5412_, 2);
lean_dec(v_unused_5443_);
v___x_5428_ = v_infoState_5412_;
v_isShared_5429_ = v_isSharedCheck_5442_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_lazyAssignment_5426_);
lean_inc(v_assignment_5425_);
lean_dec(v_infoState_5412_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5442_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5430_; lean_object* v___x_5432_; 
v___x_5430_ = l_Lean_PersistentArray_push___redArg(v_a_5400_, v_a_5407_);
if (v_isShared_5429_ == 0)
{
lean_ctor_set(v___x_5428_, 2, v___x_5430_);
v___x_5432_ = v___x_5428_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_assignment_5425_);
lean_ctor_set(v_reuseFailAlloc_5441_, 1, v_lazyAssignment_5426_);
lean_ctor_set(v_reuseFailAlloc_5441_, 2, v___x_5430_);
lean_ctor_set_uint8(v_reuseFailAlloc_5441_, sizeof(void*)*3, v_enabled_5424_);
v___x_5432_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
lean_object* v___x_5434_; 
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 7, v___x_5432_);
v___x_5434_ = v___x_5422_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_env_5413_);
lean_ctor_set(v_reuseFailAlloc_5440_, 1, v_nextMacroScope_5414_);
lean_ctor_set(v_reuseFailAlloc_5440_, 2, v_ngen_5415_);
lean_ctor_set(v_reuseFailAlloc_5440_, 3, v_auxDeclNGen_5416_);
lean_ctor_set(v_reuseFailAlloc_5440_, 4, v_traceState_5417_);
lean_ctor_set(v_reuseFailAlloc_5440_, 5, v_cache_5418_);
lean_ctor_set(v_reuseFailAlloc_5440_, 6, v_messages_5419_);
lean_ctor_set(v_reuseFailAlloc_5440_, 7, v___x_5432_);
lean_ctor_set(v_reuseFailAlloc_5440_, 8, v_snapshotTasks_5420_);
v___x_5434_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5438_; 
v___x_5435_ = lean_st_ref_set(v___y_5391_, v___x_5434_);
v___x_5436_ = lean_box(0);
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v___x_5436_);
v___x_5438_ = v___x_5409_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v___x_5436_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5453_; 
lean_dec_ref(v_a_5400_);
v_a_5446_ = lean_ctor_get(v___x_5406_, 0);
v_isSharedCheck_5453_ = !lean_is_exclusive(v___x_5406_);
if (v_isSharedCheck_5453_ == 0)
{
v___x_5448_ = v___x_5406_;
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
else
{
lean_inc(v_a_5446_);
lean_dec(v___x_5406_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5453_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v___x_5451_; 
if (v_isShared_5449_ == 0)
{
v___x_5451_ = v___x_5448_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_a_5446_);
v___x_5451_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
return v___x_5451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object* v___y_5454_, lean_object* v_mkInfoTree_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v_a_5463_, lean_object* v_a_x3f_5464_, lean_object* v___y_5465_){
_start:
{
lean_object* v_res_5466_; 
v_res_5466_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5454_, v_mkInfoTree_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v_a_5463_, v_a_x3f_5464_);
lean_dec(v_a_x3f_5464_);
lean_dec_ref(v___y_5462_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5454_);
return v_res_5466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object* v_x_5467_, lean_object* v_mkInfoTree_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v___x_5478_; lean_object* v_infoState_5479_; uint8_t v_enabled_5480_; 
v___x_5478_ = lean_st_ref_get(v___y_5476_);
v_infoState_5479_ = lean_ctor_get(v___x_5478_, 7);
lean_inc_ref(v_infoState_5479_);
lean_dec(v___x_5478_);
v_enabled_5480_ = lean_ctor_get_uint8(v_infoState_5479_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5479_);
if (v_enabled_5480_ == 0)
{
lean_object* v___x_5481_; 
lean_dec_ref(v_mkInfoTree_5468_);
lean_inc(v___y_5476_);
lean_inc_ref(v___y_5475_);
lean_inc(v___y_5474_);
lean_inc_ref(v___y_5473_);
lean_inc(v___y_5472_);
lean_inc_ref(v___y_5471_);
lean_inc(v___y_5470_);
lean_inc_ref(v___y_5469_);
v___x_5481_ = lean_apply_9(v_x_5467_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, lean_box(0));
return v___x_5481_;
}
else
{
lean_object* v___x_5482_; lean_object* v_a_5483_; lean_object* v_r_5484_; 
v___x_5482_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5476_);
v_a_5483_ = lean_ctor_get(v___x_5482_, 0);
lean_inc(v_a_5483_);
lean_dec_ref(v___x_5482_);
lean_inc(v___y_5476_);
lean_inc_ref(v___y_5475_);
lean_inc(v___y_5474_);
lean_inc_ref(v___y_5473_);
lean_inc(v___y_5472_);
lean_inc_ref(v___y_5471_);
lean_inc(v___y_5470_);
lean_inc_ref(v___y_5469_);
v_r_5484_ = lean_apply_9(v_x_5467_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, lean_box(0));
if (lean_obj_tag(v_r_5484_) == 0)
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5509_; 
v_a_5485_ = lean_ctor_get(v_r_5484_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v_r_5484_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5487_ = v_r_5484_;
v_isShared_5488_ = v_isSharedCheck_5509_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v_r_5484_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5509_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
lean_inc(v_a_5485_);
if (v_isShared_5488_ == 0)
{
lean_ctor_set_tag(v___x_5487_, 1);
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5485_);
v___x_5490_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5491_; 
v___x_5491_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5476_, v_mkInfoTree_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v_a_5483_, v___x_5490_);
lean_dec_ref(v___x_5490_);
if (lean_obj_tag(v___x_5491_) == 0)
{
lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5498_; 
v_isSharedCheck_5498_ = !lean_is_exclusive(v___x_5491_);
if (v_isSharedCheck_5498_ == 0)
{
lean_object* v_unused_5499_; 
v_unused_5499_ = lean_ctor_get(v___x_5491_, 0);
lean_dec(v_unused_5499_);
v___x_5493_ = v___x_5491_;
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
else
{
lean_dec(v___x_5491_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5498_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v___x_5496_; 
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 0, v_a_5485_);
v___x_5496_ = v___x_5493_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5485_);
v___x_5496_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
return v___x_5496_;
}
}
}
else
{
lean_object* v_a_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5507_; 
lean_dec(v_a_5485_);
v_a_5500_ = lean_ctor_get(v___x_5491_, 0);
v_isSharedCheck_5507_ = !lean_is_exclusive(v___x_5491_);
if (v_isSharedCheck_5507_ == 0)
{
v___x_5502_ = v___x_5491_;
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_a_5500_);
lean_dec(v___x_5491_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5507_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v___x_5505_; 
if (v_isShared_5503_ == 0)
{
v___x_5505_ = v___x_5502_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5506_; 
v_reuseFailAlloc_5506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5506_, 0, v_a_5500_);
v___x_5505_ = v_reuseFailAlloc_5506_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
return v___x_5505_;
}
}
}
}
}
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; 
v_a_5510_ = lean_ctor_get(v_r_5484_, 0);
lean_inc(v_a_5510_);
lean_dec_ref_known(v_r_5484_, 1);
v___x_5511_ = lean_box(0);
v___x_5512_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5476_, v_mkInfoTree_5468_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v_a_5483_, v___x_5511_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5519_ == 0)
{
lean_object* v_unused_5520_; 
v_unused_5520_ = lean_ctor_get(v___x_5512_, 0);
lean_dec(v_unused_5520_);
v___x_5514_ = v___x_5512_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_dec(v___x_5512_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
lean_ctor_set_tag(v___x_5514_, 1);
lean_ctor_set(v___x_5514_, 0, v_a_5510_);
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5510_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
else
{
lean_object* v_a_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5528_; 
lean_dec(v_a_5510_);
v_a_5521_ = lean_ctor_get(v___x_5512_, 0);
v_isSharedCheck_5528_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5528_ == 0)
{
v___x_5523_ = v___x_5512_;
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_a_5521_);
lean_dec(v___x_5512_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5526_; 
if (v_isShared_5524_ == 0)
{
v___x_5526_ = v___x_5523_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
v___x_5526_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
return v___x_5526_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object* v_x_5529_, lean_object* v_mkInfoTree_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_){
_start:
{
lean_object* v_res_5540_; 
v_res_5540_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5529_, v_mkInfoTree_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
lean_dec(v___y_5538_);
lean_dec_ref(v___y_5537_);
lean_dec(v___y_5536_);
lean_dec_ref(v___y_5535_);
lean_dec(v___y_5534_);
lean_dec_ref(v___y_5533_);
lean_dec(v___y_5532_);
lean_dec_ref(v___y_5531_);
return v_res_5540_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object* v_upperBound_5551_, lean_object* v_enterArgsAndSeps_5552_, lean_object* v_a_5553_, lean_object* v_b_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_){
_start:
{
uint8_t v___x_5564_; 
v___x_5564_ = lean_nat_dec_lt(v_a_5553_, v_upperBound_5551_);
if (v___x_5564_ == 0)
{
lean_object* v___x_5565_; 
lean_dec(v_a_5553_);
v___x_5565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5565_, 0, v_b_5554_);
return v___x_5565_;
}
else
{
lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___y_5574_; lean_object* v___x_5603_; lean_object* v___x_5604_; uint8_t v___x_5605_; 
v___x_5566_ = lean_unsigned_to_nat(2u);
v___x_5567_ = lean_box(0);
v___x_5568_ = lean_box(0);
v___x_5569_ = lean_unsigned_to_nat(0u);
v___x_5570_ = lean_unsigned_to_nat(1u);
v___x_5571_ = lean_nat_mul(v___x_5566_, v_a_5553_);
v___x_5572_ = lean_array_get_borrowed(v___x_5567_, v_enterArgsAndSeps_5552_, v___x_5571_);
v___x_5603_ = lean_nat_add(v___x_5571_, v___x_5570_);
lean_dec(v___x_5571_);
v___x_5604_ = lean_array_get_size(v_enterArgsAndSeps_5552_);
v___x_5605_ = lean_nat_dec_lt(v___x_5603_, v___x_5604_);
if (v___x_5605_ == 0)
{
lean_dec(v___x_5603_);
v___y_5574_ = v___x_5567_;
goto v___jp_5573_;
}
else
{
lean_object* v___x_5606_; 
v___x_5606_ = lean_array_fget_borrowed(v_enterArgsAndSeps_5552_, v___x_5603_);
lean_dec(v___x_5603_);
lean_inc(v___x_5606_);
v___y_5574_ = v___x_5606_;
goto v___jp_5573_;
}
v___jp_5573_:
{
lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; 
v___x_5575_ = lean_mk_empty_array_with_capacity(v___x_5566_);
lean_inc(v___x_5572_);
v___x_5576_ = lean_array_push(v___x_5575_, v___x_5572_);
v___x_5577_ = lean_array_push(v___x_5576_, v___y_5574_);
v___x_5578_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5579_ = lean_box(2);
v___x_5580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5580_, 0, v___x_5579_);
lean_ctor_set(v___x_5580_, 1, v___x_5578_);
lean_ctor_set(v___x_5580_, 2, v___x_5577_);
v___x_5581_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5580_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v_a_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; uint8_t v___x_5588_; lean_object* v___x_5589_; lean_object* v___f_5590_; lean_object* v___f_5591_; lean_object* v___x_5592_; 
v_a_5582_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_a_5582_);
lean_dec_ref_known(v___x_5581_, 1);
v___x_5583_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0));
v___x_5584_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1));
v___x_5585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2));
v___x_5586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3));
v___x_5587_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3));
lean_inc_n(v___x_5572_, 2);
v___x_5588_ = l_Lean_Syntax_isOfKind(v___x_5572_, v___x_5587_);
v___x_5589_ = lean_box(v___x_5588_);
v___f_5590_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_5590_, 0, v___x_5589_);
lean_closure_set(v___f_5590_, 1, v___x_5568_);
lean_closure_set(v___f_5590_, 2, v___x_5572_);
lean_closure_set(v___f_5590_, 3, v___x_5569_);
lean_closure_set(v___f_5590_, 4, v___x_5583_);
lean_closure_set(v___f_5590_, 5, v___x_5584_);
lean_closure_set(v___f_5590_, 6, v___x_5585_);
lean_closure_set(v___f_5590_, 7, v___x_5586_);
lean_closure_set(v___f_5590_, 8, v___x_5578_);
v___f_5591_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5591_, 0, v_a_5582_);
v___x_5592_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5590_, v___f_5591_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v___x_5593_; 
lean_dec_ref_known(v___x_5592_, 1);
v___x_5593_ = lean_nat_add(v_a_5553_, v___x_5570_);
lean_dec(v_a_5553_);
v_a_5553_ = v___x_5593_;
v_b_5554_ = v___x_5568_;
goto _start;
}
else
{
lean_dec(v_a_5553_);
return v___x_5592_;
}
}
else
{
lean_object* v_a_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5602_; 
lean_dec(v_a_5553_);
v_a_5595_ = lean_ctor_get(v___x_5581_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v___x_5581_);
if (v_isSharedCheck_5602_ == 0)
{
v___x_5597_ = v___x_5581_;
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_a_5595_);
lean_dec(v___x_5581_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5602_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v___x_5600_; 
if (v_isShared_5598_ == 0)
{
v___x_5600_ = v___x_5597_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
v___x_5600_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
return v___x_5600_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object* v_upperBound_5607_, lean_object* v_enterArgsAndSeps_5608_, lean_object* v_a_5609_, lean_object* v_b_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_){
_start:
{
lean_object* v_res_5620_; 
v_res_5620_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5607_, v_enterArgsAndSeps_5608_, v_a_5609_, v_b_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec(v___y_5616_);
lean_dec_ref(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v___y_5613_);
lean_dec(v___y_5612_);
lean_dec_ref(v___y_5611_);
lean_dec_ref(v_enterArgsAndSeps_5608_);
lean_dec(v_upperBound_5607_);
return v_res_5620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object* v_stx_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v___x_5633_; lean_object* v_token_5634_; lean_object* v___x_5635_; lean_object* v_lbrak_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; 
v___x_5633_ = lean_unsigned_to_nat(0u);
v_token_5634_ = l_Lean_Syntax_getArg(v_stx_5623_, v___x_5633_);
v___x_5635_ = lean_unsigned_to_nat(1u);
v_lbrak_5636_ = l_Lean_Syntax_getArg(v_stx_5623_, v___x_5635_);
v___x_5637_ = lean_unsigned_to_nat(2u);
v___x_5638_ = lean_mk_empty_array_with_capacity(v___x_5637_);
v___x_5639_ = lean_array_push(v___x_5638_, v_token_5634_);
v___x_5640_ = lean_array_push(v___x_5639_, v_lbrak_5636_);
v___x_5641_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5642_ = lean_box(2);
v___x_5643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5643_, 0, v___x_5642_);
lean_ctor_set(v___x_5643_, 1, v___x_5641_);
lean_ctor_set(v___x_5643_, 2, v___x_5640_);
v___x_5644_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5643_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
if (lean_obj_tag(v___x_5644_) == 0)
{
lean_object* v_a_5645_; lean_object* v___f_5646_; lean_object* v___x_5647_; lean_object* v___f_5648_; lean_object* v___x_5649_; 
v_a_5645_ = lean_ctor_get(v___x_5644_, 0);
lean_inc(v_a_5645_);
lean_dec_ref_known(v___x_5644_, 1);
v___f_5646_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed), 11, 1);
lean_closure_set(v___f_5646_, 0, v_a_5645_);
v___x_5647_ = lean_box(0);
v___f_5648_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalEnter___closed__0));
v___x_5649_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5648_, v___f_5646_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
if (lean_obj_tag(v___x_5649_) == 0)
{
lean_object* v___x_5650_; lean_object* v_enterArgsAndSeps_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; 
lean_dec_ref_known(v___x_5649_, 1);
v___x_5650_ = l_Lean_Syntax_getArg(v_stx_5623_, v___x_5637_);
v_enterArgsAndSeps_5651_ = l_Lean_Syntax_getArgs(v___x_5650_);
lean_dec(v___x_5650_);
v___x_5652_ = lean_array_get_size(v_enterArgsAndSeps_5651_);
v___x_5653_ = lean_nat_add(v___x_5652_, v___x_5635_);
v___x_5654_ = lean_nat_shiftr(v___x_5653_, v___x_5635_);
lean_dec(v___x_5653_);
v___x_5655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v___x_5654_, v_enterArgsAndSeps_5651_, v___x_5633_, v___x_5647_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_);
lean_dec_ref(v_enterArgsAndSeps_5651_);
lean_dec(v___x_5654_);
if (lean_obj_tag(v___x_5655_) == 0)
{
lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5662_; 
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5655_);
if (v_isSharedCheck_5662_ == 0)
{
lean_object* v_unused_5663_; 
v_unused_5663_ = lean_ctor_get(v___x_5655_, 0);
lean_dec(v_unused_5663_);
v___x_5657_ = v___x_5655_;
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
else
{
lean_dec(v___x_5655_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v___x_5660_; 
if (v_isShared_5658_ == 0)
{
lean_ctor_set(v___x_5657_, 0, v___x_5647_);
v___x_5660_ = v___x_5657_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5647_);
v___x_5660_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
return v___x_5660_;
}
}
}
else
{
return v___x_5655_;
}
}
else
{
return v___x_5649_;
}
}
else
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5671_; 
v_a_5664_ = lean_ctor_get(v___x_5644_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5644_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5666_ = v___x_5644_;
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5644_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object* v_stx_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_){
_start:
{
lean_object* v_res_5682_; 
v_res_5682_ = l_Lean_Elab_Tactic_Conv_evalEnter(v_stx_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_);
lean_dec(v_a_5680_);
lean_dec_ref(v_a_5679_);
lean_dec(v_a_5678_);
lean_dec_ref(v_a_5677_);
lean_dec(v_a_5676_);
lean_dec_ref(v_a_5675_);
lean_dec(v_a_5674_);
lean_dec_ref(v_a_5673_);
lean_dec(v_stx_5672_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
lean_object* v___x_5692_; 
v___x_5692_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5690_);
return v___x_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_){
_start:
{
lean_object* v_res_5702_; 
v_res_5702_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_);
lean_dec(v___y_5700_);
lean_dec_ref(v___y_5699_);
lean_dec(v___y_5698_);
lean_dec_ref(v___y_5697_);
lean_dec(v___y_5696_);
lean_dec_ref(v___y_5695_);
lean_dec(v___y_5694_);
lean_dec_ref(v___y_5693_);
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object* v_00_u03b1_5703_, lean_object* v_x_5704_, lean_object* v_mkInfoTree_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_){
_start:
{
lean_object* v___x_5715_; 
v___x_5715_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5704_, v_mkInfoTree_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_);
return v___x_5715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object* v_00_u03b1_5716_, lean_object* v_x_5717_, lean_object* v_mkInfoTree_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_){
_start:
{
lean_object* v_res_5728_; 
v_res_5728_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(v_00_u03b1_5716_, v_x_5717_, v_mkInfoTree_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
return v_res_5728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object* v_upperBound_5729_, lean_object* v_enterArgsAndSeps_5730_, lean_object* v_inst_5731_, lean_object* v_R_5732_, lean_object* v_a_5733_, lean_object* v_b_5734_, lean_object* v_c_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_){
_start:
{
lean_object* v___x_5745_; 
v___x_5745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5729_, v_enterArgsAndSeps_5730_, v_a_5733_, v_b_5734_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object* v_upperBound_5746_, lean_object* v_enterArgsAndSeps_5747_, lean_object* v_inst_5748_, lean_object* v_R_5749_, lean_object* v_a_5750_, lean_object* v_b_5751_, lean_object* v_c_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_){
_start:
{
lean_object* v_res_5762_; 
v_res_5762_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(v_upperBound_5746_, v_enterArgsAndSeps_5747_, v_inst_5748_, v_R_5749_, v_a_5750_, v_b_5751_, v_c_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec(v___y_5754_);
lean_dec_ref(v___y_5753_);
lean_dec_ref(v_enterArgsAndSeps_5747_);
lean_dec(v_upperBound_5746_);
return v_res_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1(){
_start:
{
lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; 
v___x_5778_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1));
v___x_5780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3));
v___x_5781_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___boxed), 10, 0);
v___x_5782_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5778_, v___x_5779_, v___x_5780_, v___x_5781_);
return v___x_5782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object* v_a_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
return v_res_5784_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Congr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Congr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
