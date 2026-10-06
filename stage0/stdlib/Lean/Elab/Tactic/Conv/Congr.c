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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "'apply implies_congr' unexpected result"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "implies_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 71, 54, 187, 9, 73, 178, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`congr` conv tactic failed to create congruence theorem"};
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
static const lean_string_object l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "invalid `congr` conv tactic, application or implication expected"};
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
static const lean_string_object l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "invalid `arg 0` conv tactic, application expected"};
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
static const lean_string_object l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "invalid `fun` conv tactic, application expected"};
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`apply funext` unexpected result"};
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
static const lean_string_object l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "invalid `ext` conv tactic, function or arrow expected"};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_Tactic_Conv_evalEnter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
lean_object* v___x_92_; lean_object* v_env_93_; uint8_t v___x_94_; lean_object* v_env_95_; lean_object* v___x_96_; lean_object* v_toCold_97_; lean_object* v_mctx_98_; lean_object* v_lctx_99_; lean_object* v_options_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = 0;
v_env_95_ = l_Lean_Environment_setRecordingDeps(v_env_93_, v___x_94_);
v___x_96_ = lean_st_ref_get(v___y_88_);
v_toCold_97_ = lean_ctor_get(v___y_89_, 0);
v_mctx_98_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_mctx_98_);
lean_dec(v___x_96_);
v_lctx_99_ = lean_ctor_get(v___y_87_, 2);
v_options_100_ = lean_ctor_get(v_toCold_97_, 2);
lean_inc_ref(v_options_100_);
lean_inc_ref(v_lctx_99_);
v___x_101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_101_, 0, v_env_95_);
lean_ctor_set(v___x_101_, 1, v_mctx_98_);
lean_ctor_set(v___x_101_, 2, v_lctx_99_);
lean_ctor_set(v___x_101_, 3, v_options_100_);
v___x_102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_msgData_86_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0___boxed(lean_object* v_msgData_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msgData_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_ref_117_; lean_object* v___x_118_; lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_127_; 
v_ref_117_ = lean_ctor_get(v___y_114_, 2);
v___x_118_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
v_a_119_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_127_ == 0)
{
v___x_121_ = v___x_118_;
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_118_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_127_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_125_; 
lean_inc(v_ref_117_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v_ref_117_);
lean_ctor_set(v___x_123_, 1, v_a_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 1);
lean_ctor_set(v___x_121_, 0, v___x_123_);
v___x_125_ = v___x_121_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg___boxed(lean_object* v_msg_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0));
v___x_137_ = l_Lean_stringToMessageData(v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object* v_mvarId_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___y_152_; lean_object* v___y_153_; lean_object* v___y_154_; lean_object* v___y_155_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3));
v___x_159_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_158_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref_known(v___x_159_, 1);
v___x_161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4));
v___x_162_ = lean_box(0);
v___x_163_ = l_Lean_MVarId_apply(v_mvarId_145_, v_a_160_, v___x_161_, v___x_162_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
if (lean_obj_tag(v_a_164_) == 1)
{
lean_object* v_tail_165_; 
v_tail_165_ = lean_ctor_get(v_a_164_, 1);
lean_inc(v_tail_165_);
if (lean_obj_tag(v_tail_165_) == 1)
{
lean_object* v_tail_166_; 
v_tail_166_ = lean_ctor_get(v_tail_165_, 1);
lean_inc(v_tail_166_);
if (lean_obj_tag(v_tail_166_) == 1)
{
lean_object* v_tail_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_212_; 
v_tail_167_ = lean_ctor_get(v_tail_166_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_tail_166_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v_tail_166_, 0);
lean_dec(v_unused_213_);
v___x_169_ = v_tail_166_;
v_isShared_170_ = v_isSharedCheck_212_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_tail_167_);
lean_dec(v_tail_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_212_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
if (lean_obj_tag(v_tail_167_) == 1)
{
lean_object* v_tail_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_210_; 
v_tail_171_ = lean_ctor_get(v_tail_167_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_tail_167_);
if (v_isSharedCheck_210_ == 0)
{
lean_object* v_unused_211_; 
v_unused_211_ = lean_ctor_get(v_tail_167_, 0);
lean_dec(v_unused_211_);
v___x_173_ = v_tail_167_;
v_isShared_174_ = v_isSharedCheck_210_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_tail_171_);
lean_dec(v_tail_167_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_210_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
if (lean_obj_tag(v_tail_171_) == 0)
{
lean_object* v_head_175_; lean_object* v_head_176_; lean_object* v___x_177_; 
v_head_175_ = lean_ctor_get(v_a_164_, 0);
lean_inc(v_head_175_);
lean_dec_ref_known(v_a_164_, 2);
v_head_176_ = lean_ctor_get(v_tail_165_, 0);
lean_inc(v_head_176_);
lean_dec_ref_known(v_tail_165_, 2);
v___x_177_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_175_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref_known(v___x_177_, 1);
v___x_179_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_176_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_193_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_193_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_193_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v_a_180_);
v___x_185_ = v___x_173_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_tail_171_);
v___x_185_ = v_reuseFailAlloc_192_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_187_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v___x_185_);
lean_ctor_set(v___x_169_, 0, v_a_178_);
v___x_187_ = v___x_169_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_187_);
v___x_189_ = v___x_182_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_a_178_);
lean_del_object(v___x_173_);
lean_del_object(v___x_169_);
v_a_194_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_179_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_179_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_head_176_);
lean_del_object(v___x_173_);
lean_del_object(v___x_169_);
v_a_202_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_177_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_177_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_del_object(v___x_173_);
lean_dec(v_tail_171_);
lean_del_object(v___x_169_);
lean_dec_ref_known(v_tail_165_, 2);
lean_dec_ref_known(v_a_164_, 2);
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
v___y_154_ = v_a_148_;
v___y_155_ = v_a_149_;
goto v___jp_151_;
}
}
}
else
{
lean_del_object(v___x_169_);
lean_dec(v_tail_167_);
lean_dec_ref_known(v_tail_165_, 2);
lean_dec_ref_known(v_a_164_, 2);
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
v___y_154_ = v_a_148_;
v___y_155_ = v_a_149_;
goto v___jp_151_;
}
}
}
else
{
lean_dec_ref_known(v_tail_165_, 2);
lean_dec(v_tail_166_);
lean_dec_ref_known(v_a_164_, 2);
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
v___y_154_ = v_a_148_;
v___y_155_ = v_a_149_;
goto v___jp_151_;
}
}
else
{
lean_dec_ref_known(v_a_164_, 2);
lean_dec(v_tail_165_);
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
v___y_154_ = v_a_148_;
v___y_155_ = v_a_149_;
goto v___jp_151_;
}
}
else
{
lean_dec(v_a_164_);
v___y_152_ = v_a_146_;
v___y_153_ = v_a_147_;
v___y_154_ = v_a_148_;
v___y_155_ = v_a_149_;
goto v___jp_151_;
}
}
else
{
return v___x_163_;
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_mvarId_145_);
v_a_214_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_159_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_159_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
v___jp_151_:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1);
v___x_157_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_156_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object* v_mvarId_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object* v_00_u03b1_229_, lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object* v_00_u03b1_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(v_00_u03b1_237_, v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object* v_e_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = l_Lean_Expr_isArrow(v_e_245_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_box(v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = l_Lean_Expr_bindingDomain_x21(v_e_245_);
v___x_255_ = l_Lean_Meta_isProp(v___x_254_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; uint8_t v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v___x_257_ = lean_unbox(v_a_256_);
if (v___x_257_ == 0)
{
return v___x_255_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref_known(v___x_255_, 1);
v___x_258_ = l_Lean_Expr_bindingBody_x21(v_e_245_);
v___x_259_ = l_Lean_Meta_isProp(v___x_258_, v_a_246_, v_a_247_, v_a_248_, v_a_249_);
return v___x_259_;
}
}
else
{
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v_e_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec_ref(v_e_260_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_8175__overap_275_; lean_object* v___x_276_; 
v___f_274_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_8175__overap_275_ = lean_panic_fn_borrowed(v___f_274_, v_msg_268_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
v___x_276_ = lean_apply_5(v___x_8175__overap_275_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, lean_box(0));
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___boxed(lean_object* v_msg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(lean_object* v___x_284_, lean_object* v_fst_285_, lean_object* v_fst_286_, lean_object* v_fst_287_, lean_object* v_snd_288_, lean_object* v_tag_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
lean_inc_ref(v___x_284_);
v___x_295_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_284_, v_tag_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_320_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_320_ == 0)
{
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_319_; 
v_fst_300_ = lean_ctor_get(v_a_296_, 0);
v_snd_301_ = lean_ctor_get(v_a_296_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v_a_296_);
if (v_isSharedCheck_319_ == 0)
{
v___x_303_ = v_a_296_;
v_isShared_304_ = v_isSharedCheck_319_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_snd_301_);
lean_inc(v_fst_300_);
lean_dec(v_a_296_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_319_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
lean_inc(v_fst_300_);
v___x_305_ = l_Lean_Expr_app___override(v_fst_285_, v_fst_300_);
lean_inc(v_snd_301_);
v___x_306_ = l_Lean_mkApp3(v_fst_286_, v___x_284_, v_fst_300_, v_snd_301_);
v___x_307_ = l_Lean_Expr_mvarId_x21(v_snd_301_);
lean_dec(v_snd_301_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
v___x_309_ = lean_array_push(v_fst_287_, v___x_308_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v_snd_288_);
lean_ctor_set(v___x_303_, 0, v___x_309_);
v___x_311_ = v___x_303_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_309_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_snd_288_);
v___x_311_ = v_reuseFailAlloc_318_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_306_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_305_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_314_);
v___x_316_ = v___x_298_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_snd_288_);
lean_dec(v_fst_287_);
lean_dec(v_fst_286_);
lean_dec(v_fst_285_);
lean_dec_ref(v___x_284_);
v_a_321_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_295_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_295_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1___boxed(lean_object* v___x_329_, lean_object* v_fst_330_, lean_object* v_fst_331_, lean_object* v_fst_332_, lean_object* v_snd_333_, lean_object* v_tag_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_329_, v_fst_330_, v_fst_331_, v_fst_332_, v_snd_333_, v_tag_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_340_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_344_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_345_ = lean_unsigned_to_nat(30u);
v___x_346_ = lean_unsigned_to_nat(68u);
v___x_347_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1));
v___x_348_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_349_ = l_mkPanicMessageWithDecl(v___x_348_, v___x_347_, v___x_346_, v___x_345_, v___x_344_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(lean_object* v_fst_350_, lean_object* v_snd_351_, lean_object* v_fst_352_, lean_object* v_fst_353_, lean_object* v_00___354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3);
v___x_361_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_360_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_372_; 
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_361_, 0);
lean_dec(v_unused_373_);
v___x_363_ = v___x_361_;
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
else
{
lean_dec(v___x_361_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_372_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_fst_350_);
lean_ctor_set(v___x_365_, 1, v_snd_351_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_fst_352_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_fst_353_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_368_);
v___x_370_ = v___x_363_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_fst_353_);
lean_dec(v_fst_352_);
lean_dec(v_snd_351_);
lean_dec(v_fst_350_);
v_a_374_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_361_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_361_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___boxed(lean_object* v_fst_382_, lean_object* v_snd_383_, lean_object* v_fst_384_, lean_object* v_fst_385_, lean_object* v_00___386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_382_, v_snd_383_, v_fst_384_, v_fst_385_, v_00___386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(lean_object* v_upperBound_393_, lean_object* v_args_394_, uint8_t v_nameSubgoals_395_, lean_object* v_origTag_396_, lean_object* v_a_397_, lean_object* v___x_398_, uint8_t v_addImplicitArgs_399_, lean_object* v_a_400_, lean_object* v_b_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_a_408_; lean_object* v___y_413_; uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_lt(v_a_400_, v_upperBound_393_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v_b_401_);
return v___x_433_;
}
else
{
lean_object* v_snd_434_; lean_object* v_snd_435_; lean_object* v_fst_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_577_; 
v_snd_434_ = lean_ctor_get(v_b_401_, 1);
lean_inc(v_snd_434_);
v_snd_435_ = lean_ctor_get(v_snd_434_, 1);
lean_inc(v_snd_435_);
v_fst_436_ = lean_ctor_get(v_b_401_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_b_401_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v_b_401_, 1);
lean_dec(v_unused_578_);
v___x_438_ = v_b_401_;
v_isShared_439_ = v_isSharedCheck_577_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_fst_436_);
lean_dec(v_b_401_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_577_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_fst_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_575_; 
v_fst_440_ = lean_ctor_get(v_snd_434_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_snd_434_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_snd_434_, 1);
lean_dec(v_unused_576_);
v___x_442_ = v_snd_434_;
v_isShared_443_ = v_isSharedCheck_575_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_fst_440_);
lean_dec(v_snd_434_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_575_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_574_; 
v_fst_444_ = lean_ctor_get(v_snd_435_, 0);
v_snd_445_ = lean_ctor_get(v_snd_435_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_snd_435_);
if (v_isSharedCheck_574_ == 0)
{
v___x_447_ = v_snd_435_;
v_isShared_448_ = v_isSharedCheck_574_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_snd_445_);
lean_inc(v_fst_444_);
lean_dec(v_snd_435_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_574_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_paramInfo_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_paramInfo_449_ = lean_ctor_get(v_a_397_, 0);
v___x_450_ = l_Lean_instInhabitedExpr;
v___x_451_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_452_ = lean_array_get_borrowed(v___x_450_, v_args_394_, v_a_400_);
v___x_453_ = lean_array_get_borrowed(v___x_451_, v_paramInfo_449_, v_a_400_);
v___x_454_ = lean_array_fget_borrowed(v___x_398_, v_a_400_);
v___x_455_ = lean_unbox(v___x_454_);
switch(v___x_455_)
{
case 1:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
v___x_456_ = lean_box(0);
v___x_457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_444_, v_snd_445_, v_fst_440_, v_fst_436_, v___x_456_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
v___y_413_ = v___x_457_;
goto v___jp_412_;
}
case 2:
{
if (v_addImplicitArgs_399_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_453_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc_n(v___x_452_, 2);
v___x_484_ = l_Lean_Expr_app___override(v_fst_436_, v___x_452_);
v___x_485_ = l_Lean_Meta_mkEqRefl(v___x_452_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
lean_inc_n(v___x_452_, 2);
v___x_487_ = l_Lean_mkApp3(v_fst_440_, v___x_452_, v___x_452_, v_a_486_);
if (v_isShared_448_ == 0)
{
v___x_489_ = v___x_447_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_fst_444_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_snd_445_);
v___x_489_ = v_reuseFailAlloc_496_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_489_);
lean_ctor_set(v___x_442_, 0, v___x_487_);
v___x_491_ = v___x_442_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_491_);
lean_ctor_set(v___x_438_, 0, v___x_484_);
v___x_493_ = v___x_438_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
v_a_408_ = v___x_493_;
goto v___jp_407_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v___x_484_);
lean_del_object(v___x_447_);
lean_dec(v_snd_445_);
lean_dec(v_fst_444_);
lean_del_object(v___x_442_);
lean_dec(v_fst_440_);
lean_del_object(v___x_438_);
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_497_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_485_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_485_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
goto v___jp_458_;
}
}
else
{
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
goto v___jp_458_;
}
v___jp_458_:
{
if (v_nameSubgoals_395_ == 0)
{
lean_object* v___x_459_; 
lean_inc(v_origTag_396_);
lean_inc(v___x_452_);
v___x_459_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_452_, v_fst_436_, v_fst_440_, v_fst_444_, v_snd_445_, v_origTag_396_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
v___y_413_ = v___x_459_;
goto v___jp_412_;
}
else
{
lean_object* v___x_460_; 
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc(v_fst_440_);
v___x_460_ = lean_infer_type(v_fst_440_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_462_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref_known(v___x_460_, 1);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_462_ = lean_whnf(v_a_461_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v___x_464_ = l_Lean_Expr_bindingName_x21(v_a_463_);
lean_dec(v_a_463_);
lean_inc(v_origTag_396_);
v___x_465_ = l_Lean_Meta_appendTag(v_origTag_396_, v___x_464_);
lean_dec(v___x_464_);
lean_inc(v___x_452_);
v___x_466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_452_, v_fst_436_, v_fst_440_, v_fst_444_, v_snd_445_, v___x_465_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
v___y_413_ = v___x_466_;
goto v___jp_412_;
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_snd_445_);
lean_dec(v_fst_444_);
lean_dec(v_fst_440_);
lean_dec(v_fst_436_);
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_467_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_462_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_462_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_snd_445_);
lean_dec(v_fst_444_);
lean_dec(v_fst_440_);
lean_dec(v_fst_436_);
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_475_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_460_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_460_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
v___x_505_ = lean_box(0);
v___x_506_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_444_, v_snd_445_, v_fst_440_, v_fst_436_, v___x_505_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
v___y_413_ = v___x_506_;
goto v___jp_412_;
}
case 5:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_inc(v___x_452_);
v___x_507_ = l_Lean_Expr_app___override(v_fst_440_, v___x_452_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
lean_inc_ref(v___x_507_);
v___x_508_ = lean_infer_type(v___x_507_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_510_ = lean_whnf(v_a_509_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = l_Lean_Expr_bindingDomain_x21(v_a_511_);
lean_dec(v_a_511_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = 0;
v___x_515_ = lean_box(0);
v___x_516_ = l_Lean_Meta_mkFreshExprMVar(v___x_513_, v___x_514_, v___x_515_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc_n(v_a_517_, 3);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = l_Lean_Expr_app___override(v_fst_436_, v_a_517_);
v___x_519_ = l_Lean_Expr_app___override(v___x_507_, v_a_517_);
v___x_520_ = l_Lean_Expr_mvarId_x21(v_a_517_);
lean_dec(v_a_517_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
v___x_522_ = lean_array_push(v_snd_445_, v___x_521_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_522_);
v___x_524_ = v___x_447_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_fst_444_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v___x_522_);
v___x_524_ = v_reuseFailAlloc_531_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
lean_object* v___x_526_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_524_);
lean_ctor_set(v___x_442_, 0, v___x_519_);
v___x_526_ = v___x_442_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_530_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_526_);
lean_ctor_set(v___x_438_, 0, v___x_518_);
v___x_528_ = v___x_438_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_a_408_ = v___x_528_;
goto v___jp_407_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v___x_507_);
lean_del_object(v___x_447_);
lean_dec(v_snd_445_);
lean_dec(v_fst_444_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_532_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_516_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_516_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v___x_507_);
lean_del_object(v___x_447_);
lean_dec(v_snd_445_);
lean_dec(v_fst_444_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_540_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_510_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_510_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v___x_507_);
lean_del_object(v___x_447_);
lean_dec(v_snd_445_);
lean_dec(v_fst_444_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
lean_dec(v_fst_436_);
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_548_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_508_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_508_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
default: 
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_inc_n(v___x_452_, 2);
v___x_556_ = l_Lean_Expr_app___override(v_fst_436_, v___x_452_);
v___x_557_ = l_Lean_Expr_app___override(v_fst_440_, v___x_452_);
if (v_addImplicitArgs_399_ == 0)
{
uint8_t v___x_570_; 
v___x_570_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_453_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_del_object(v___x_447_);
lean_del_object(v___x_442_);
lean_del_object(v___x_438_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_fst_444_);
lean_ctor_set(v___x_571_, 1, v_snd_445_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_557_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_556_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v_a_408_ = v___x_573_;
goto v___jp_407_;
}
else
{
goto v___jp_558_;
}
}
else
{
goto v___jp_558_;
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_array_push(v_fst_444_, v___x_559_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_560_);
v___x_562_ = v___x_447_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_snd_445_);
v___x_562_ = v_reuseFailAlloc_569_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_564_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_562_);
lean_ctor_set(v___x_442_, 0, v___x_557_);
v___x_564_ = v___x_442_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_562_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_564_);
lean_ctor_set(v___x_438_, 0, v___x_556_);
v___x_566_ = v___x_438_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v_a_408_ = v___x_566_;
goto v___jp_407_;
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
v___jp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(1u);
v___x_410_ = lean_nat_add(v_a_400_, v___x_409_);
lean_dec(v_a_400_);
v_a_400_ = v___x_410_;
v_b_401_ = v_a_408_;
goto _start;
}
v___jp_412_:
{
if (lean_obj_tag(v___y_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_423_; 
v_a_414_ = lean_ctor_get(v___y_413_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___y_413_);
if (v_isSharedCheck_423_ == 0)
{
v___x_416_ = v___y_413_;
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___y_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
if (lean_obj_tag(v_a_414_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; 
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_418_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v_a_414_, 1);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_a_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
else
{
lean_object* v_a_422_; 
lean_del_object(v___x_416_);
v_a_422_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v_a_414_, 1);
v_a_408_ = v_a_422_;
goto v___jp_407_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v_a_400_);
lean_dec(v_origTag_396_);
v_a_424_ = lean_ctor_get(v___y_413_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___y_413_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___y_413_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___y_413_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___boxed(lean_object* v_upperBound_579_, lean_object* v_args_580_, lean_object* v_nameSubgoals_581_, lean_object* v_origTag_582_, lean_object* v_a_583_, lean_object* v___x_584_, lean_object* v_addImplicitArgs_585_, lean_object* v_a_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
uint8_t v_nameSubgoals_boxed_593_; uint8_t v_addImplicitArgs_boxed_594_; lean_object* v_res_595_; 
v_nameSubgoals_boxed_593_ = lean_unbox(v_nameSubgoals_581_);
v_addImplicitArgs_boxed_594_ = lean_unbox(v_addImplicitArgs_585_);
v_res_595_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_579_, v_args_580_, v_nameSubgoals_boxed_593_, v_origTag_582_, v_a_583_, v___x_584_, v_addImplicitArgs_boxed_594_, v_a_586_, v_b_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec_ref(v___x_584_);
lean_dec_ref(v_a_583_);
lean_dec_ref(v_args_580_);
lean_dec(v_upperBound_579_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(lean_object* v_a_596_, lean_object* v_b_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_array_603_; lean_object* v_start_604_; lean_object* v_stop_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_620_; 
v_array_603_ = lean_ctor_get(v_a_596_, 0);
v_start_604_ = lean_ctor_get(v_a_596_, 1);
v_stop_605_ = lean_ctor_get(v_a_596_, 2);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_620_ == 0)
{
v___x_607_ = v_a_596_;
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_stop_605_);
lean_inc(v_start_604_);
lean_inc(v_array_603_);
lean_dec(v_a_596_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_620_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
uint8_t v___x_609_; 
v___x_609_ = lean_nat_dec_lt(v_start_604_, v_stop_605_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
lean_del_object(v___x_607_);
lean_dec(v_stop_605_);
lean_dec(v_start_604_);
lean_dec_ref(v_array_603_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v_b_597_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_add(v_start_604_, v___x_611_);
lean_inc_ref(v_array_603_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_612_);
v___x_614_ = v___x_607_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_array_603_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_stop_605_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_array_fget(v_array_603_, v_start_604_);
lean_dec(v_start_604_);
lean_dec_ref(v_array_603_);
v___x_616_ = l_Lean_Meta_mkCongrFun(v_b_597_, v___x_615_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v_a_596_ = v___x_614_;
v_b_597_ = v_a_617_;
goto _start;
}
else
{
lean_dec_ref(v___x_614_);
return v___x_616_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg___boxed(lean_object* v_a_621_, lean_object* v_b_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_621_, v_b_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_628_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2));
v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(lean_object* v_origTag_636_, lean_object* v_f_637_, lean_object* v_args_638_, uint8_t v_addImplicitArgs_639_, uint8_t v_nameSubgoals_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_proof_647_; lean_object* v_mvarIdsNew_648_; lean_object* v_mvarIdsNewInsts_649_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_array_get_size(v_args_638_);
lean_inc_ref(v_f_637_);
v___x_654_ = l_Lean_Meta_getFunInfoNArgs(v_f_637_, v___x_653_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
lean_inc_ref(v_f_637_);
v___x_656_ = l_Lean_Meta_getCongrSimpKinds(v_f_637_, v_a_655_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; uint8_t v___x_658_; lean_object* v___x_659_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = 0;
lean_inc(v_a_655_);
lean_inc_ref(v_f_637_);
v___x_659_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_637_, v_a_655_, v_a_657_, v___x_658_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
if (lean_obj_tag(v_a_660_) == 1)
{
lean_object* v_val_661_; lean_object* v_proof_662_; lean_object* v_argKinds_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_val_661_ = lean_ctor_get(v_a_660_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v_a_660_, 1);
v_proof_662_ = lean_ctor_get(v_val_661_, 1);
lean_inc_ref(v_proof_662_);
v_argKinds_663_ = lean_ctor_get(v_val_661_, 2);
lean_inc_ref(v_argKinds_663_);
lean_dec(v_val_661_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_array_get_size(v_argKinds_663_);
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1));
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v_proof_662_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_f_637_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
lean_inc(v_origTag_636_);
v___x_669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v___x_665_, v_args_638_, v_nameSubgoals_640_, v_origTag_636_, v_a_655_, v_argKinds_663_, v_addImplicitArgs_639_, v___x_664_, v___x_668_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec_ref(v_argKinds_663_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v_snd_671_; lean_object* v_snd_672_; lean_object* v_fst_673_; lean_object* v_fst_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v_lower_682_; lean_object* v_upper_683_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___x_721_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v_snd_671_ = lean_ctor_get(v_a_670_, 1);
lean_inc(v_snd_671_);
v_snd_672_ = lean_ctor_get(v_snd_671_, 1);
lean_inc(v_snd_672_);
v_fst_673_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_fst_673_);
lean_dec(v_a_670_);
v_fst_674_ = lean_ctor_get(v_snd_671_, 0);
lean_inc(v_fst_674_);
lean_dec(v_snd_671_);
v_fst_675_ = lean_ctor_get(v_snd_672_, 0);
lean_inc(v_fst_675_);
v_snd_676_ = lean_ctor_get(v_snd_672_, 1);
lean_inc(v_snd_676_);
lean_dec(v_snd_672_);
v___x_721_ = lean_nat_dec_lt(v___x_665_, v___x_653_);
if (v___x_721_ == 0)
{
lean_dec(v_fst_673_);
lean_dec(v_a_655_);
lean_dec_ref(v_args_638_);
lean_dec(v_origTag_636_);
v_proof_647_ = v_fst_674_;
v_mvarIdsNew_648_ = v_fst_675_;
v_mvarIdsNewInsts_649_ = v_snd_676_;
goto v___jp_646_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = lean_nat_dec_eq(v___x_665_, v___x_664_);
if (v___x_722_ == 0)
{
v___y_715_ = v_a_641_;
v___y_716_ = v_a_642_;
v___y_717_ = v_a_643_;
v___y_718_ = v_a_644_;
goto v___jp_714_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_724_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_723_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_dec_ref_known(v___x_724_, 1);
v___y_715_ = v_a_641_;
v___y_716_ = v_a_642_;
v___y_717_ = v_a_643_;
v___y_718_ = v_a_644_;
goto v___jp_714_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_snd_676_);
lean_dec(v_fst_675_);
lean_dec(v_fst_674_);
lean_dec(v_fst_673_);
lean_dec(v_a_655_);
lean_dec_ref(v_args_638_);
lean_dec(v_origTag_636_);
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
v___jp_677_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = l_Array_toSubarray___redArg(v_args_638_, v_lower_682_, v_upper_683_);
lean_inc_ref(v___x_684_);
v___x_685_ = l_Subarray_copy___redArg(v___x_684_);
v___x_686_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_636_, v_fst_673_, v___x_685_, v_addImplicitArgs_639_, v_nameSubgoals_640_, v___y_678_, v___y_679_, v___y_681_, v___y_680_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_snd_688_; lean_object* v_fst_689_; lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_692_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v_snd_688_ = lean_ctor_get(v_a_687_, 1);
lean_inc(v_snd_688_);
v_fst_689_ = lean_ctor_get(v_a_687_, 0);
lean_inc(v_fst_689_);
lean_dec(v_a_687_);
v_fst_690_ = lean_ctor_get(v_snd_688_, 0);
lean_inc(v_fst_690_);
v_snd_691_ = lean_ctor_get(v_snd_688_, 1);
lean_inc(v_snd_691_);
lean_dec(v_snd_688_);
v___x_692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_684_, v_fst_674_, v___y_678_, v___y_679_, v___y_681_, v___y_680_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = l_Lean_Meta_mkEqTrans(v_a_693_, v_fst_689_, v___y_678_, v___y_679_, v___y_681_, v___y_680_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = l_Array_append___redArg(v_fst_675_, v_fst_690_);
lean_dec(v_fst_690_);
v___x_697_ = l_Array_append___redArg(v_snd_676_, v_snd_691_);
lean_dec(v_snd_691_);
v_proof_647_ = v_a_695_;
v_mvarIdsNew_648_ = v___x_696_;
v_mvarIdsNewInsts_649_ = v___x_697_;
goto v___jp_646_;
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_snd_691_);
lean_dec(v_fst_690_);
lean_dec(v_snd_676_);
lean_dec(v_fst_675_);
v_a_698_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_694_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_694_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_snd_691_);
lean_dec(v_fst_690_);
lean_dec(v_fst_689_);
lean_dec(v_snd_676_);
lean_dec(v_fst_675_);
v_a_706_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_692_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_692_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_dec_ref(v___x_684_);
lean_dec(v_snd_676_);
lean_dec(v_fst_675_);
lean_dec(v_fst_674_);
return v___x_686_;
}
}
v___jp_714_:
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = l_Lean_Meta_FunInfo_getArity(v_a_655_);
lean_dec(v_a_655_);
v___x_720_ = lean_nat_dec_le(v___x_719_, v___x_664_);
if (v___x_720_ == 0)
{
v___y_678_ = v___y_715_;
v___y_679_ = v___y_716_;
v___y_680_ = v___y_718_;
v___y_681_ = v___y_717_;
v_lower_682_ = v___x_719_;
v_upper_683_ = v___x_653_;
goto v___jp_677_;
}
else
{
lean_dec(v___x_719_);
v___y_678_ = v___y_715_;
v___y_679_ = v___y_716_;
v___y_680_ = v___y_718_;
v___y_681_ = v___y_717_;
v_lower_682_ = v___x_664_;
v_upper_683_ = v___x_653_;
goto v___jp_677_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_a_655_);
lean_dec_ref(v_args_638_);
lean_dec(v_origTag_636_);
v_a_733_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_669_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_669_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_a_660_);
lean_dec(v_a_655_);
lean_dec_ref(v_args_638_);
lean_dec_ref(v_f_637_);
lean_dec(v_origTag_636_);
v___x_741_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_742_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_741_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_742_;
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_a_655_);
lean_dec_ref(v_args_638_);
lean_dec_ref(v_f_637_);
lean_dec(v_origTag_636_);
v_a_743_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_659_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_659_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_a_655_);
lean_dec_ref(v_args_638_);
lean_dec_ref(v_f_637_);
lean_dec(v_origTag_636_);
v_a_751_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_656_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_656_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec_ref(v_args_638_);
lean_dec_ref(v_f_637_);
lean_dec(v_origTag_636_);
v_a_759_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_654_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_654_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
v___jp_646_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_mvarIdsNew_648_);
lean_ctor_set(v___x_650_, 1, v_mvarIdsNewInsts_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v_proof_647_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___boxed(lean_object* v_origTag_767_, lean_object* v_f_768_, lean_object* v_args_769_, lean_object* v_addImplicitArgs_770_, lean_object* v_nameSubgoals_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
uint8_t v_addImplicitArgs_boxed_777_; uint8_t v_nameSubgoals_boxed_778_; lean_object* v_res_779_; 
v_addImplicitArgs_boxed_777_ = lean_unbox(v_addImplicitArgs_770_);
v_nameSubgoals_boxed_778_ = lean_unbox(v_nameSubgoals_771_);
v_res_779_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_767_, v_f_768_, v_args_769_, v_addImplicitArgs_boxed_777_, v_nameSubgoals_boxed_778_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_object* v_inst_780_, lean_object* v_R_781_, lean_object* v_a_782_, lean_object* v_b_783_, lean_object* v_c_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_782_, v_b_783_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___boxed(lean_object* v_inst_791_, lean_object* v_R_792_, lean_object* v_a_793_, lean_object* v_b_794_, lean_object* v_c_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(v_inst_791_, v_R_792_, v_a_793_, v_b_794_, v_c_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(lean_object* v_upperBound_802_, lean_object* v_args_803_, uint8_t v_nameSubgoals_804_, lean_object* v_origTag_805_, lean_object* v_a_806_, lean_object* v___x_807_, uint8_t v_addImplicitArgs_808_, lean_object* v_inst_809_, lean_object* v_R_810_, lean_object* v_a_811_, lean_object* v_b_812_, lean_object* v_c_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_802_, v_args_803_, v_nameSubgoals_804_, v_origTag_805_, v_a_806_, v___x_807_, v_addImplicitArgs_808_, v_a_811_, v_b_812_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_820_ = _args[0];
lean_object* v_args_821_ = _args[1];
lean_object* v_nameSubgoals_822_ = _args[2];
lean_object* v_origTag_823_ = _args[3];
lean_object* v_a_824_ = _args[4];
lean_object* v___x_825_ = _args[5];
lean_object* v_addImplicitArgs_826_ = _args[6];
lean_object* v_inst_827_ = _args[7];
lean_object* v_R_828_ = _args[8];
lean_object* v_a_829_ = _args[9];
lean_object* v_b_830_ = _args[10];
lean_object* v_c_831_ = _args[11];
lean_object* v___y_832_ = _args[12];
lean_object* v___y_833_ = _args[13];
lean_object* v___y_834_ = _args[14];
lean_object* v___y_835_ = _args[15];
lean_object* v___y_836_ = _args[16];
_start:
{
uint8_t v_nameSubgoals_boxed_837_; uint8_t v_addImplicitArgs_boxed_838_; lean_object* v_res_839_; 
v_nameSubgoals_boxed_837_ = lean_unbox(v_nameSubgoals_822_);
v_addImplicitArgs_boxed_838_ = lean_unbox(v_addImplicitArgs_826_);
v_res_839_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(v_upperBound_820_, v_args_821_, v_nameSubgoals_boxed_837_, v_origTag_823_, v_a_824_, v___x_825_, v_addImplicitArgs_boxed_838_, v_inst_827_, v_R_828_, v_a_829_, v_b_830_, v_c_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec_ref(v___x_825_);
lean_dec_ref(v_a_824_);
lean_dec_ref(v_args_821_);
lean_dec(v_upperBound_820_);
return v_res_839_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0));
v___x_842_ = l_Lean_stringToMessageData(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2));
v___x_845_ = l_Lean_stringToMessageData(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4));
v___x_848_ = l_Lean_stringToMessageData(v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(lean_object* v_tacticName_849_, lean_object* v_rhs_850_, lean_object* v_rhs_x27_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
lean_inc_ref(v_rhs_x27_851_);
lean_inc_ref(v_rhs_850_);
v___x_857_ = l_Lean_Meta_isExprDefEqGuarded(v_rhs_850_, v_rhs_x27_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_879_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_879_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_879_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_879_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
uint8_t v___x_862_; 
v___x_862_ = lean_unbox(v_a_858_);
lean_dec(v_a_858_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_del_object(v___x_860_);
v___x_863_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_864_ = l_Lean_stringToMessageData(v_tacticName_849_);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_indentExpr(v_rhs_850_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Lean_indentExpr(v_rhs_x27_851_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_873_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec_ref(v_rhs_x27_851_);
lean_dec_ref(v_rhs_850_);
lean_dec_ref(v_tacticName_849_);
v___x_875_ = lean_box(0);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_875_);
v___x_877_ = v___x_860_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v_rhs_x27_851_);
lean_dec_ref(v_rhs_850_);
lean_dec_ref(v_tacticName_849_);
v_a_880_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_857_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_857_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___boxed(lean_object* v_tacticName_888_, lean_object* v_rhs_889_, lean_object* v_rhs_x27_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_888_, v_rhs_889_, v_rhs_x27_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
return v_res_896_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(lean_object* v_tacticName_906_, lean_object* v_rhs_907_, lean_object* v_proof_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
v___x_914_ = lean_infer_type(v_proof_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_a_909_);
v___x_916_ = lean_whnf(v_a_915_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1));
v___x_919_ = lean_unsigned_to_nat(3u);
v___x_920_ = l_Lean_Expr_isAppOfArity(v_a_917_, v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec(v_a_917_);
lean_dec_ref(v_rhs_907_);
v___x_921_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_922_ = l_Lean_stringToMessageData(v_tacticName_906_);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_925_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_926_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = l_Lean_Expr_appArg_x21(v_a_917_);
lean_dec(v_a_917_);
v___x_928_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_906_, v_rhs_907_, v___x_927_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_928_;
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_rhs_907_);
lean_dec_ref(v_tacticName_906_);
v_a_929_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_916_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_916_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_rhs_907_);
lean_dec_ref(v_tacticName_906_);
v_a_937_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_914_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_914_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___boxed(lean_object* v_tacticName_945_, lean_object* v_rhs_946_, lean_object* v_proof_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_945_, v_rhs_946_, v_proof_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(lean_object* v_e_954_, lean_object* v___y_955_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = l_Lean_Expr_hasMVar(v_e_954_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; 
v___x_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_958_, 0, v_e_954_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v_mctx_960_; lean_object* v___x_961_; lean_object* v_fst_962_; lean_object* v_snd_963_; lean_object* v___x_964_; lean_object* v_cache_965_; lean_object* v_zetaDeltaFVarIds_966_; lean_object* v_postponed_967_; lean_object* v_diag_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v___x_959_ = lean_st_ref_get(v___y_955_);
v_mctx_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_mctx_960_);
lean_dec(v___x_959_);
v___x_961_ = l_Lean_instantiateMVarsCore(v_mctx_960_, v_e_954_);
v_fst_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_fst_962_);
v_snd_963_ = lean_ctor_get(v___x_961_, 1);
lean_inc(v_snd_963_);
lean_dec_ref(v___x_961_);
v___x_964_ = lean_st_ref_take(v___y_955_);
v_cache_965_ = lean_ctor_get(v___x_964_, 1);
v_zetaDeltaFVarIds_966_ = lean_ctor_get(v___x_964_, 2);
v_postponed_967_ = lean_ctor_get(v___x_964_, 3);
v_diag_968_ = lean_ctor_get(v___x_964_, 4);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_977_ == 0)
{
lean_object* v_unused_978_; 
v_unused_978_ = lean_ctor_get(v___x_964_, 0);
lean_dec(v_unused_978_);
v___x_970_ = v___x_964_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_diag_968_);
lean_inc(v_postponed_967_);
lean_inc(v_zetaDeltaFVarIds_966_);
lean_inc(v_cache_965_);
lean_dec(v___x_964_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_snd_963_);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_snd_963_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_cache_965_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_zetaDeltaFVarIds_966_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_postponed_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_diag_968_);
v___x_973_ = v_reuseFailAlloc_976_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_st_ref_put(v___y_955_, v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_fst_962_);
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg___boxed(lean_object* v_e_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_979_, v___y_980_);
lean_dec(v___y_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(lean_object* v_e_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_983_, v___y_985_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___boxed(lean_object* v_e_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(v_e_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(lean_object* v_mvarId_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_997_, v_x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
v_a_1013_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1004_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1004_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg___boxed(lean_object* v_mvarId_1021_, lean_object* v_x_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1021_, v_x_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_object* v_00_u03b1_1029_, lean_object* v_mvarId_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1030_, v_x_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_mvarId_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(v_00_u03b1_1038_, v_mvarId_1039_, v_x_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
if (lean_obj_tag(v_a_1047_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = l_List_reverse___redArg(v_a_1048_);
return v___x_1049_;
}
else
{
lean_object* v_head_1050_; lean_object* v_tail_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1060_; 
v_head_1050_ = lean_ctor_get(v_a_1047_, 0);
v_tail_1051_ = lean_ctor_get(v_a_1047_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_a_1047_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1053_ = v_a_1047_;
v_isShared_1054_ = v_isSharedCheck_1060_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_tail_1051_);
lean_inc(v_head_1050_);
lean_dec(v_a_1047_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1060_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_head_1050_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 1, v_a_1048_);
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_a_1048_);
v___x_1057_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
v_a_1047_ = v_tail_1051_;
v_a_1048_ = v___x_1057_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v_ks_1065_; lean_object* v_vs_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1090_; 
v_ks_1065_ = lean_ctor_get(v_x_1061_, 0);
v_vs_1066_ = lean_ctor_get(v_x_1061_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_x_1061_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1068_ = v_x_1061_;
v_isShared_1069_ = v_isSharedCheck_1090_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_vs_1066_);
lean_inc(v_ks_1065_);
lean_dec(v_x_1061_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1090_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_array_get_size(v_ks_1065_);
v___x_1071_ = lean_nat_dec_lt(v_x_1062_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_dec(v_x_1062_);
v___x_1072_ = lean_array_push(v_ks_1065_, v_x_1063_);
v___x_1073_ = lean_array_push(v_vs_1066_, v_x_1064_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___x_1073_);
lean_ctor_set(v___x_1068_, 0, v___x_1072_);
v___x_1075_ = v___x_1068_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
else
{
lean_object* v_k_x27_1077_; uint8_t v___x_1078_; 
v_k_x27_1077_ = lean_array_fget_borrowed(v_ks_1065_, v_x_1062_);
v___x_1078_ = l_Lean_instBEqMVarId_beq(v_x_1063_, v_k_x27_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1080_; 
if (v_isShared_1069_ == 0)
{
v___x_1080_ = v___x_1068_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_ks_1065_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_vs_1066_);
v___x_1080_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_nat_add(v_x_1062_, v___x_1081_);
lean_dec(v_x_1062_);
v_x_1061_ = v___x_1080_;
v_x_1062_ = v___x_1082_;
goto _start;
}
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1085_ = lean_array_fset(v_ks_1065_, v_x_1062_, v_x_1063_);
v___x_1086_ = lean_array_fset(v_vs_1066_, v_x_1062_, v_x_1064_);
lean_dec(v_x_1062_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___x_1086_);
lean_ctor_set(v___x_1068_, 0, v___x_1085_);
v___x_1088_ = v___x_1068_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_n_1091_, lean_object* v_k_1092_, lean_object* v_v_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_n_1091_, v___x_1094_, v_k_1092_, v_v_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1097_, size_t v_x_1098_, size_t v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v_es_1102_; size_t v___x_1103_; size_t v___x_1104_; lean_object* v_j_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_es_1102_ = lean_ctor_get(v_x_1097_, 0);
v___x_1103_ = ((size_t)31ULL);
v___x_1104_ = lean_usize_land(v_x_1098_, v___x_1103_);
v_j_1105_ = lean_usize_to_nat(v___x_1104_);
v___x_1106_ = lean_array_get_size(v_es_1102_);
v___x_1107_ = lean_nat_dec_lt(v_j_1105_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_dec(v_j_1105_);
lean_dec(v_x_1101_);
lean_dec(v_x_1100_);
return v_x_1097_;
}
else
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1146_; 
lean_inc_ref(v_es_1102_);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; 
v_unused_1147_ = lean_ctor_get(v_x_1097_, 0);
lean_dec(v_unused_1147_);
v___x_1109_ = v_x_1097_;
v_isShared_1110_ = v_isSharedCheck_1146_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_x_1097_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1146_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_v_1111_; lean_object* v___x_1112_; lean_object* v_xs_x27_1113_; lean_object* v___y_1115_; 
v_v_1111_ = lean_array_fget(v_es_1102_, v_j_1105_);
v___x_1112_ = lean_box(0);
v_xs_x27_1113_ = lean_array_fset(v_es_1102_, v_j_1105_, v___x_1112_);
switch(lean_obj_tag(v_v_1111_))
{
case 0:
{
lean_object* v_key_1120_; lean_object* v_val_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1131_; 
v_key_1120_ = lean_ctor_get(v_v_1111_, 0);
v_val_1121_ = lean_ctor_get(v_v_1111_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_v_1111_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1123_ = v_v_1111_;
v_isShared_1124_ = v_isSharedCheck_1131_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_val_1121_);
lean_inc(v_key_1120_);
lean_dec(v_v_1111_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1131_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_instBEqMVarId_beq(v_x_1100_, v_key_1120_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_del_object(v___x_1123_);
v___x_1126_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1120_, v_val_1121_, v_x_1100_, v_x_1101_);
v___x_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
v___y_1115_ = v___x_1127_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1129_; 
lean_dec(v_val_1121_);
lean_dec(v_key_1120_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v_x_1101_);
lean_ctor_set(v___x_1123_, 0, v_x_1100_);
v___x_1129_ = v___x_1123_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_x_1100_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_x_1101_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
v___y_1115_ = v___x_1129_;
goto v___jp_1114_;
}
}
}
}
case 1:
{
lean_object* v_node_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1144_; 
v_node_1132_ = lean_ctor_get(v_v_1111_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_v_1111_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1134_ = v_v_1111_;
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_node_1132_);
lean_dec(v_v_1111_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1144_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
size_t v___x_1136_; size_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1136_ = ((size_t)5ULL);
v___x_1137_ = lean_usize_shift_right(v_x_1098_, v___x_1136_);
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = lean_usize_add(v_x_1099_, v___x_1138_);
v___x_1140_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_node_1132_, v___x_1137_, v___x_1139_, v_x_1100_, v_x_1101_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1140_);
v___x_1142_ = v___x_1134_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
v___y_1115_ = v___x_1142_;
goto v___jp_1114_;
}
}
}
default: 
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_x_1100_);
lean_ctor_set(v___x_1145_, 1, v_x_1101_);
v___y_1115_ = v___x_1145_;
goto v___jp_1114_;
}
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_array_fset(v_xs_x27_1113_, v_j_1105_, v___y_1115_);
lean_dec(v_j_1105_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1116_);
v___x_1118_ = v___x_1109_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
else
{
lean_object* v_ks_1148_; lean_object* v_vs_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1167_; 
v_ks_1148_ = lean_ctor_get(v_x_1097_, 0);
v_vs_1149_ = lean_ctor_get(v_x_1097_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1151_ = v_x_1097_;
v_isShared_1152_ = v_isSharedCheck_1167_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_vs_1149_);
lean_inc(v_ks_1148_);
lean_dec(v_x_1097_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1167_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_ks_1148_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_vs_1149_);
v___x_1154_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v_newNode_1155_; size_t v___x_1156_; uint8_t v___x_1157_; 
v_newNode_1155_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v___x_1154_, v_x_1100_, v_x_1101_);
v___x_1156_ = ((size_t)7ULL);
v___x_1157_ = lean_usize_dec_le(v___x_1156_, v_x_1099_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1158_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1155_);
v___x_1159_ = lean_unsigned_to_nat(4u);
v___x_1160_ = lean_nat_dec_lt(v___x_1158_, v___x_1159_);
lean_dec(v___x_1158_);
if (v___x_1160_ == 0)
{
lean_object* v_ks_1161_; lean_object* v_vs_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_ks_1161_ = lean_ctor_get(v_newNode_1155_, 0);
lean_inc_ref(v_ks_1161_);
v_vs_1162_ = lean_ctor_get(v_newNode_1155_, 1);
lean_inc_ref(v_vs_1162_);
lean_dec_ref(v_newNode_1155_);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1165_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_x_1099_, v_ks_1161_, v_vs_1162_, v___x_1163_, v___x_1164_);
lean_dec_ref(v_vs_1162_);
lean_dec_ref(v_ks_1161_);
return v___x_1165_;
}
else
{
return v_newNode_1155_;
}
}
else
{
return v_newNode_1155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(size_t v_depth_1168_, lean_object* v_keys_1169_, lean_object* v_vals_1170_, lean_object* v_i_1171_, lean_object* v_entries_1172_){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = lean_array_get_size(v_keys_1169_);
v___x_1174_ = lean_nat_dec_lt(v_i_1171_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_dec(v_i_1171_);
return v_entries_1172_;
}
else
{
lean_object* v_k_1175_; lean_object* v_v_1176_; uint64_t v___x_1177_; size_t v_h_1178_; size_t v___x_1179_; lean_object* v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v_h_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_k_1175_ = lean_array_fget_borrowed(v_keys_1169_, v_i_1171_);
v_v_1176_ = lean_array_fget_borrowed(v_vals_1170_, v_i_1171_);
v___x_1177_ = l_Lean_instHashableMVarId_hash(v_k_1175_);
v_h_1178_ = lean_uint64_to_usize(v___x_1177_);
v___x_1179_ = ((size_t)5ULL);
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_sub(v_depth_1168_, v___x_1181_);
v___x_1183_ = lean_usize_mul(v___x_1179_, v___x_1182_);
v_h_1184_ = lean_usize_shift_right(v_h_1178_, v___x_1183_);
v___x_1185_ = lean_nat_add(v_i_1171_, v___x_1180_);
lean_dec(v_i_1171_);
lean_inc(v_v_1176_);
lean_inc(v_k_1175_);
v___x_1186_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_entries_1172_, v_h_1184_, v_depth_1168_, v_k_1175_, v_v_1176_);
v_i_1171_ = v___x_1185_;
v_entries_1172_ = v___x_1186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1188_, lean_object* v_keys_1189_, lean_object* v_vals_1190_, lean_object* v_i_1191_, lean_object* v_entries_1192_){
_start:
{
size_t v_depth_boxed_1193_; lean_object* v_res_1194_; 
v_depth_boxed_1193_ = lean_unbox_usize(v_depth_1188_);
lean_dec(v_depth_1188_);
v_res_1194_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_boxed_1193_, v_keys_1189_, v_vals_1190_, v_i_1191_, v_entries_1192_);
lean_dec_ref(v_vals_1190_);
lean_dec_ref(v_keys_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
size_t v_x_2729__boxed_1200_; size_t v_x_2730__boxed_1201_; lean_object* v_res_1202_; 
v_x_2729__boxed_1200_ = lean_unbox_usize(v_x_1196_);
lean_dec(v_x_1196_);
v_x_2730__boxed_1201_ = lean_unbox_usize(v_x_1197_);
lean_dec(v_x_1197_);
v_res_1202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1195_, v_x_2729__boxed_1200_, v_x_2730__boxed_1201_, v_x_1198_, v_x_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(lean_object* v_x_1203_, lean_object* v_x_1204_, lean_object* v_x_1205_){
_start:
{
uint64_t v___x_1206_; size_t v___x_1207_; size_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = l_Lean_instHashableMVarId_hash(v_x_1204_);
v___x_1207_ = lean_uint64_to_usize(v___x_1206_);
v___x_1208_ = ((size_t)1ULL);
v___x_1209_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1203_, v___x_1207_, v___x_1208_, v_x_1204_, v_x_1205_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(lean_object* v_mvarId_1210_, lean_object* v_val_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v_mctx_1215_; lean_object* v_cache_1216_; lean_object* v_zetaDeltaFVarIds_1217_; lean_object* v_postponed_1218_; lean_object* v_diag_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1249_; 
v___x_1214_ = lean_st_ref_take(v___y_1212_);
v_mctx_1215_ = lean_ctor_get(v___x_1214_, 0);
v_cache_1216_ = lean_ctor_get(v___x_1214_, 1);
v_zetaDeltaFVarIds_1217_ = lean_ctor_get(v___x_1214_, 2);
v_postponed_1218_ = lean_ctor_get(v___x_1214_, 3);
v_diag_1219_ = lean_ctor_get(v___x_1214_, 4);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1221_ = v___x_1214_;
v_isShared_1222_ = v_isSharedCheck_1249_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_diag_1219_);
lean_inc(v_postponed_1218_);
lean_inc(v_zetaDeltaFVarIds_1217_);
lean_inc(v_cache_1216_);
lean_inc(v_mctx_1215_);
lean_dec(v___x_1214_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1249_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_depth_1223_; lean_object* v_levelAssignDepth_1224_; lean_object* v_lmvarCounter_1225_; lean_object* v_mvarCounter_1226_; lean_object* v_lDecls_1227_; lean_object* v_decls_1228_; lean_object* v_userNames_1229_; lean_object* v_lAssignment_1230_; lean_object* v_eAssignment_1231_; lean_object* v_dAssignment_1232_; lean_object* v_instanceTypedMVars_1233_; lean_object* v_synthNormMemo_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1248_; 
v_depth_1223_ = lean_ctor_get(v_mctx_1215_, 0);
v_levelAssignDepth_1224_ = lean_ctor_get(v_mctx_1215_, 1);
v_lmvarCounter_1225_ = lean_ctor_get(v_mctx_1215_, 2);
v_mvarCounter_1226_ = lean_ctor_get(v_mctx_1215_, 3);
v_lDecls_1227_ = lean_ctor_get(v_mctx_1215_, 4);
v_decls_1228_ = lean_ctor_get(v_mctx_1215_, 5);
v_userNames_1229_ = lean_ctor_get(v_mctx_1215_, 6);
v_lAssignment_1230_ = lean_ctor_get(v_mctx_1215_, 7);
v_eAssignment_1231_ = lean_ctor_get(v_mctx_1215_, 8);
v_dAssignment_1232_ = lean_ctor_get(v_mctx_1215_, 9);
v_instanceTypedMVars_1233_ = lean_ctor_get(v_mctx_1215_, 10);
v_synthNormMemo_1234_ = lean_ctor_get(v_mctx_1215_, 11);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_mctx_1215_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1236_ = v_mctx_1215_;
v_isShared_1237_ = v_isSharedCheck_1248_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_synthNormMemo_1234_);
lean_inc(v_instanceTypedMVars_1233_);
lean_inc(v_dAssignment_1232_);
lean_inc(v_eAssignment_1231_);
lean_inc(v_lAssignment_1230_);
lean_inc(v_userNames_1229_);
lean_inc(v_decls_1228_);
lean_inc(v_lDecls_1227_);
lean_inc(v_mvarCounter_1226_);
lean_inc(v_lmvarCounter_1225_);
lean_inc(v_levelAssignDepth_1224_);
lean_inc(v_depth_1223_);
lean_dec(v_mctx_1215_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1248_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_1231_, v_mvarId_1210_, v_val_1211_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 8, v___x_1239_);
v___x_1241_ = v___x_1236_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_depth_1223_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_levelAssignDepth_1224_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_lmvarCounter_1225_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_mvarCounter_1226_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_lDecls_1227_);
lean_ctor_set(v_reuseFailAlloc_1247_, 5, v_decls_1228_);
lean_ctor_set(v_reuseFailAlloc_1247_, 6, v_userNames_1229_);
lean_ctor_set(v_reuseFailAlloc_1247_, 7, v_lAssignment_1230_);
lean_ctor_set(v_reuseFailAlloc_1247_, 8, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1247_, 9, v_dAssignment_1232_);
lean_ctor_set(v_reuseFailAlloc_1247_, 10, v_instanceTypedMVars_1233_);
lean_ctor_set(v_reuseFailAlloc_1247_, 11, v_synthNormMemo_1234_);
v___x_1241_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1241_);
v___x_1243_ = v___x_1221_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_cache_1216_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_zetaDeltaFVarIds_1217_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_postponed_1218_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_diag_1219_);
v___x_1243_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_st_ref_put(v___y_1212_, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1238_);
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg___boxed(lean_object* v_mvarId_1250_, lean_object* v_val_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1250_, v_val_1251_, v___y_1252_);
lean_dec(v___y_1252_);
return v_res_1254_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0));
v___x_1257_ = l_Lean_stringToMessageData(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1258_; lean_object* v_dummy_1259_; 
v___x_1258_ = lean_box(0);
v_dummy_1259_ = l_Lean_Expr_sort___override(v___x_1258_);
return v_dummy_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0(lean_object* v_mvarId_1261_, uint8_t v_addImplicitArgs_1262_, uint8_t v_nameSubgoals_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
lean_inc(v_mvarId_1261_);
v___x_1269_ = l_Lean_MVarId_getTag(v_mvarId_1261_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
lean_inc(v_mvarId_1261_);
v___x_1271_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1261_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v_fst_1273_; lean_object* v_snd_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1361_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v_fst_1273_ = lean_ctor_get(v_a_1272_, 0);
v_snd_1274_ = lean_ctor_get(v_a_1272_, 1);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_a_1272_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1276_ = v_a_1272_;
v_isShared_1277_ = v_isSharedCheck_1361_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_snd_1274_);
lean_inc(v_fst_1273_);
lean_dec(v_a_1272_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1361_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v_a_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1278_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1273_, v___y_1265_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = l_Lean_Expr_cleanupAnnotations(v_a_1279_);
v___x_1281_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v___x_1280_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; uint8_t v___x_1283_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v___x_1283_ = lean_unbox(v_a_1282_);
lean_dec(v_a_1282_);
if (v___x_1283_ == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec(v_snd_1274_);
lean_dec(v_a_1270_);
lean_dec(v_mvarId_1261_);
v___x_1285_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1);
v___x_1286_ = l_Lean_indentExpr(v___x_1280_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set_tag(v___x_1276_, 7);
lean_ctor_set(v___x_1276_, 1, v___x_1286_);
lean_ctor_set(v___x_1276_, 0, v___x_1285_);
v___x_1288_ = v___x_1276_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1288_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v_dummy_1292_; lean_object* v_nargs_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_del_object(v___x_1276_);
v___x_1291_ = l_Lean_Expr_getAppFn(v___x_1280_);
v_dummy_1292_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1293_ = l_Lean_Expr_getAppNumArgs(v___x_1280_);
lean_inc(v_nargs_1293_);
v___x_1294_ = lean_mk_array(v_nargs_1293_, v_dummy_1292_);
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_sub(v_nargs_1293_, v___x_1295_);
lean_dec(v_nargs_1293_);
v___x_1297_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1280_, v___x_1294_, v___x_1296_);
v___x_1298_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_a_1270_, v___x_1291_, v___x_1297_, v_addImplicitArgs_1262_, v_nameSubgoals_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v_snd_1300_; lean_object* v_fst_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v_snd_1300_ = lean_ctor_get(v_a_1299_, 1);
lean_inc(v_snd_1300_);
v_fst_1301_ = lean_ctor_get(v_a_1299_, 0);
lean_inc_n(v_fst_1301_, 2);
lean_dec(v_a_1299_);
v_fst_1302_ = lean_ctor_get(v_snd_1300_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v_snd_1300_, 1);
lean_inc(v_snd_1303_);
lean_dec(v_snd_1300_);
v___x_1304_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3));
v___x_1305_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v___x_1304_, v_snd_1274_, v_fst_1301_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref_known(v___x_1305_, 1);
v___x_1306_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1261_, v_fst_1301_, v___y_1265_);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1306_, 0);
lean_dec(v_unused_1317_);
v___x_1308_ = v___x_1306_;
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
else
{
lean_dec(v___x_1306_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1316_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1310_ = lean_array_to_list(v_fst_1302_);
v___x_1311_ = lean_array_to_list(v_snd_1303_);
v___x_1312_ = l_List_appendTR___redArg(v___x_1310_, v___x_1311_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1312_);
v___x_1314_ = v___x_1308_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_snd_1303_);
lean_dec(v_fst_1302_);
lean_dec(v_fst_1301_);
lean_dec(v_mvarId_1261_);
v_a_1318_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1305_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1305_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_snd_1274_);
lean_dec(v_mvarId_1261_);
v_a_1326_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1298_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1298_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
else
{
lean_object* v___x_1334_; 
lean_dec_ref(v___x_1280_);
lean_del_object(v___x_1276_);
lean_dec(v_snd_1274_);
lean_dec(v_a_1270_);
v___x_1334_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_1261_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1344_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(v_a_1335_, v___x_1339_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1340_);
v___x_1342_ = v___x_1337_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1334_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1334_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v___x_1280_);
lean_del_object(v___x_1276_);
lean_dec(v_snd_1274_);
lean_dec(v_a_1270_);
lean_dec(v_mvarId_1261_);
v_a_1353_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1281_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1281_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1270_);
lean_dec(v_mvarId_1261_);
v_a_1362_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1271_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1271_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_mvarId_1261_);
v_a_1370_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1269_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1269_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed(lean_object* v_mvarId_1378_, lean_object* v_addImplicitArgs_1379_, lean_object* v_nameSubgoals_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1386_; uint8_t v_nameSubgoals_boxed_1387_; lean_object* v_res_1388_; 
v_addImplicitArgs_boxed_1386_ = lean_unbox(v_addImplicitArgs_1379_);
v_nameSubgoals_boxed_1387_ = lean_unbox(v_nameSubgoals_1380_);
v_res_1388_ = l_Lean_Elab_Tactic_Conv_congr___lam__0(v_mvarId_1378_, v_addImplicitArgs_boxed_1386_, v_nameSubgoals_boxed_1387_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr(lean_object* v_mvarId_1389_, uint8_t v_addImplicitArgs_1390_, uint8_t v_nameSubgoals_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; 
v___x_1397_ = lean_box(v_addImplicitArgs_1390_);
v___x_1398_ = lean_box(v_nameSubgoals_1391_);
lean_inc(v_mvarId_1389_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1399_, 0, v_mvarId_1389_);
lean_closure_set(v___f_1399_, 1, v___x_1397_);
lean_closure_set(v___f_1399_, 2, v___x_1398_);
v___x_1400_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1389_, v___f_1399_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___boxed(lean_object* v_mvarId_1401_, lean_object* v_addImplicitArgs_1402_, lean_object* v_nameSubgoals_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1409_; uint8_t v_nameSubgoals_boxed_1410_; lean_object* v_res_1411_; 
v_addImplicitArgs_boxed_1409_ = lean_unbox(v_addImplicitArgs_1402_);
v_nameSubgoals_boxed_1410_ = lean_unbox(v_nameSubgoals_1403_);
v_res_1411_ = l_Lean_Elab_Tactic_Conv_congr(v_mvarId_1401_, v_addImplicitArgs_boxed_1409_, v_nameSubgoals_boxed_1410_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(lean_object* v_mvarId_1412_, lean_object* v_val_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1412_, v_val_1413_, v___y_1415_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___boxed(lean_object* v_mvarId_1420_, lean_object* v_val_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(v_mvarId_1420_, v_val_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1(lean_object* v_00_u03b2_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_x_1429_, v_x_1430_, v_x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1433_, lean_object* v_x_1434_, size_t v_x_1435_, size_t v_x_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1434_, v_x_1435_, v_x_1436_, v_x_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_){
_start:
{
size_t v_x_3223__boxed_1446_; size_t v_x_3224__boxed_1447_; lean_object* v_res_1448_; 
v_x_3223__boxed_1446_ = lean_unbox_usize(v_x_1442_);
lean_dec(v_x_1442_);
v_x_3224__boxed_1447_ = lean_unbox_usize(v_x_1443_);
lean_dec(v_x_1443_);
v_res_1448_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(v_00_u03b2_1440_, v_x_1441_, v_x_3223__boxed_1446_, v_x_3224__boxed_1447_, v_x_1444_, v_x_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1449_, lean_object* v_n_1450_, lean_object* v_k_1451_, lean_object* v_v_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v_n_1450_, v_k_1451_, v_v_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1454_, size_t v_depth_1455_, lean_object* v_keys_1456_, lean_object* v_vals_1457_, lean_object* v_heq_1458_, lean_object* v_i_1459_, lean_object* v_entries_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_1455_, v_keys_1456_, v_vals_1457_, v_i_1459_, v_entries_1460_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1462_, lean_object* v_depth_1463_, lean_object* v_keys_1464_, lean_object* v_vals_1465_, lean_object* v_heq_1466_, lean_object* v_i_1467_, lean_object* v_entries_1468_){
_start:
{
size_t v_depth_boxed_1469_; lean_object* v_res_1470_; 
v_depth_boxed_1469_ = lean_unbox_usize(v_depth_1463_);
lean_dec(v_depth_1463_);
v_res_1470_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(v_00_u03b2_1462_, v_depth_boxed_1469_, v_keys_1464_, v_vals_1465_, v_heq_1466_, v_i_1467_, v_entries_1468_);
lean_dec_ref(v_vals_1465_);
lean_dec_ref(v_keys_1464_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_x_1472_, v_x_1473_, v_x_1474_, v_x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
if (lean_obj_tag(v_a_1477_) == 0)
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_array_to_list(v_a_1478_);
return v___x_1479_;
}
else
{
lean_object* v_head_1480_; 
v_head_1480_ = lean_ctor_get(v_a_1477_, 0);
if (lean_obj_tag(v_head_1480_) == 0)
{
lean_object* v_tail_1481_; 
v_tail_1481_ = lean_ctor_get(v_a_1477_, 1);
lean_inc(v_tail_1481_);
lean_dec_ref_known(v_a_1477_, 2);
v_a_1477_ = v_tail_1481_;
goto _start;
}
else
{
lean_object* v_tail_1483_; lean_object* v_val_1484_; lean_object* v___x_1485_; 
lean_inc_ref(v_head_1480_);
v_tail_1483_ = lean_ctor_get(v_a_1477_, 1);
lean_inc(v_tail_1483_);
lean_dec_ref_known(v_a_1477_, 2);
v_val_1484_ = lean_ctor_get(v_head_1480_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v_head_1480_, 1);
v___x_1485_ = lean_array_push(v_a_1478_, v_val_1484_);
v_a_1477_ = v_tail_1483_;
v_a_1478_ = v___x_1485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg(lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; uint8_t v___x_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1497_ = 0;
v___x_1498_ = 1;
v___x_1499_ = l_Lean_Elab_Tactic_Conv_congr(v_a_1496_, v___x_1497_, v___x_1498_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0));
v___x_1502_ = l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(v_a_1500_, v___x_1501_);
v___x_1503_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1502_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
return v___x_1503_;
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1499_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1499_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1495_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1495_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___boxed(lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr(lean_object* v_x_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1529_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___boxed(lean_object* v_x_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Elab_Tactic_Conv_evalCongr(v_x_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_x_1538_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1(){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1563_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0));
v___x_1565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1566_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCongr___boxed), 10, 0);
v___x_1567_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1563_, v___x_1564_, v___x_1565_, v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___boxed(lean_object* v_a_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3(){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6));
v___x_1598_ = l_Lean_addBuiltinDeclarationRanges(v___x_1596_, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___boxed(lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(lean_object* v_as_1601_, size_t v_i_1602_, size_t v_stop_1603_, lean_object* v_b_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_eq(v_i_1602_, v_stop_1603_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_array_uget_borrowed(v_as_1601_, v_i_1602_);
lean_inc(v___x_1611_);
v___x_1612_ = l_Lean_Meta_mkCongrFun(v_b_1604_, v___x_1611_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; size_t v___x_1614_; size_t v___x_1615_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = lean_usize_add(v_i_1602_, v___x_1614_);
v_i_1602_ = v___x_1615_;
v_b_1604_ = v_a_1613_;
goto _start;
}
else
{
return v___x_1612_;
}
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_b_1604_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0___boxed(lean_object* v_as_1618_, lean_object* v_i_1619_, lean_object* v_stop_1620_, lean_object* v_b_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
size_t v_i_boxed_1627_; size_t v_stop_boxed_1628_; lean_object* v_res_1629_; 
v_i_boxed_1627_ = lean_unbox_usize(v_i_1619_);
lean_dec(v_i_1619_);
v_stop_boxed_1628_ = lean_unbox_usize(v_stop_1620_);
lean_dec(v_stop_1620_);
v_res_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_as_1618_, v_i_boxed_1627_, v_stop_boxed_1628_, v_b_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v_as_1618_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(lean_object* v_mvarId_1631_, lean_object* v_snd_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
if (lean_obj_tag(v_x_1633_) == 5)
{
lean_object* v_fn_1641_; lean_object* v_arg_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_fn_1641_ = lean_ctor_get(v_x_1633_, 0);
lean_inc_ref(v_fn_1641_);
v_arg_1642_ = lean_ctor_get(v_x_1633_, 1);
lean_inc_ref(v_arg_1642_);
lean_dec_ref_known(v_x_1633_, 2);
v___x_1643_ = lean_array_set(v_x_1634_, v_x_1635_, v_arg_1642_);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_nat_sub(v_x_1635_, v___x_1644_);
lean_dec(v_x_1635_);
v_x_1633_ = v_fn_1641_;
v_x_1634_ = v___x_1643_;
v_x_1635_ = v___x_1645_;
goto _start;
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_x_1635_);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_x_1633_, v___x_1647_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v_fst_1650_; lean_object* v_snd_1651_; lean_object* v_a_1653_; lean_object* v___y_1676_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v_fst_1650_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_fst_1650_);
v_snd_1651_ = lean_ctor_get(v_a_1649_, 1);
lean_inc(v_snd_1651_);
lean_dec(v_a_1649_);
v___x_1686_ = lean_unsigned_to_nat(0u);
v___x_1687_ = lean_array_get_size(v_x_1634_);
v___x_1688_ = lean_nat_dec_lt(v___x_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_inc(v_snd_1651_);
v_a_1653_ = v_snd_1651_;
goto v___jp_1652_;
}
else
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_nat_dec_le(v___x_1687_, v___x_1687_);
if (v___x_1689_ == 0)
{
if (v___x_1688_ == 0)
{
lean_inc(v_snd_1651_);
v_a_1653_ = v_snd_1651_;
goto v___jp_1652_;
}
else
{
size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = lean_usize_of_nat(v___x_1687_);
lean_inc(v_snd_1651_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1634_, v___x_1690_, v___x_1691_, v_snd_1651_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
v___y_1676_ = v___x_1692_;
goto v___jp_1675_;
}
}
else
{
size_t v___x_1693_; size_t v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((size_t)0ULL);
v___x_1694_ = lean_usize_of_nat(v___x_1687_);
lean_inc(v_snd_1651_);
v___x_1695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1634_, v___x_1693_, v___x_1694_, v_snd_1651_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
v___y_1676_ = v___x_1695_;
goto v___jp_1675_;
}
}
v___jp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1654_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1631_, v_a_1653_, v___y_1637_);
lean_dec_ref(v___x_1654_);
v___x_1655_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0));
v___x_1656_ = l_Lean_mkAppN(v_fst_1650_, v_x_1634_);
lean_dec_ref(v_x_1634_);
v___x_1657_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_1655_, v_snd_1632_, v___x_1656_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1665_; 
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v___x_1657_, 0);
lean_dec(v_unused_1666_);
v___x_1659_ = v___x_1657_;
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
else
{
lean_dec(v___x_1657_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1665_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = l_Lean_Expr_mvarId_x21(v_snd_1651_);
lean_dec(v_snd_1651_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v___x_1661_);
v___x_1663_ = v___x_1659_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v_snd_1651_);
v_a_1667_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1657_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1657_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
v___jp_1675_:
{
if (lean_obj_tag(v___y_1676_) == 0)
{
lean_object* v_a_1677_; 
v_a_1677_ = lean_ctor_get(v___y_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___y_1676_, 1);
v_a_1653_ = v_a_1677_;
goto v___jp_1652_;
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_snd_1651_);
lean_dec(v_fst_1650_);
lean_dec_ref(v_x_1634_);
lean_dec_ref(v_snd_1632_);
lean_dec(v_mvarId_1631_);
v_a_1678_ = lean_ctor_get(v___y_1676_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___y_1676_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___y_1676_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___y_1676_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v_x_1634_);
lean_dec_ref(v_snd_1632_);
lean_dec(v_mvarId_1631_);
v_a_1696_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1648_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1648_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___boxed(lean_object* v_mvarId_1704_, lean_object* v_snd_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1704_, v_snd_1705_, v_x_1706_, v_x_1707_, v_x_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1714_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0));
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(lean_object* v_mvarId_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
lean_inc(v_mvarId_1718_);
v___x_1724_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v_fst_1726_; lean_object* v_snd_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1760_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v_fst_1726_ = lean_ctor_get(v_a_1725_, 0);
v_snd_1727_ = lean_ctor_get(v_a_1725_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_a_1725_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1729_ = v_a_1725_;
v_isShared_1730_ = v_isSharedCheck_1760_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_snd_1727_);
lean_inc(v_fst_1726_);
lean_dec(v_a_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1760_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v_a_1732_; lean_object* v___x_1733_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; uint8_t v___x_1745_; 
v___x_1731_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1726_, v___y_1720_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = l_Lean_Expr_cleanupAnnotations(v_a_1732_);
v___x_1745_ = l_Lean_Expr_isApp(v___x_1733_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_dec(v_snd_1727_);
lean_dec(v_mvarId_1718_);
v___x_1746_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1);
v___x_1747_ = l_Lean_indentExpr(v___x_1733_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set_tag(v___x_1729_, 7);
lean_ctor_set(v___x_1729_, 1, v___x_1747_);
lean_ctor_set(v___x_1729_, 0, v___x_1746_);
v___x_1749_ = v___x_1729_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
v___x_1750_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1749_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_del_object(v___x_1729_);
v___y_1735_ = v___y_1719_;
v___y_1736_ = v___y_1720_;
v___y_1737_ = v___y_1721_;
v___y_1738_ = v___y_1722_;
goto v___jp_1734_;
}
v___jp_1734_:
{
lean_object* v_dummy_1739_; lean_object* v_nargs_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_dummy_1739_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1740_ = l_Lean_Expr_getAppNumArgs(v___x_1733_);
lean_inc(v_nargs_1740_);
v___x_1741_ = lean_mk_array(v_nargs_1740_, v_dummy_1739_);
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_sub(v_nargs_1740_, v___x_1742_);
lean_dec(v_nargs_1740_);
v___x_1744_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1718_, v_snd_1727_, v___x_1733_, v___x_1741_, v___x_1743_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_mvarId_1718_);
v_a_1761_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1724_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1724_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed(lean_object* v_mvarId_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(v_mvarId_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN(lean_object* v_mvarId_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v___f_1782_; lean_object* v___x_1783_; 
lean_inc(v_mvarId_1776_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1782_, 0, v_mvarId_1776_);
v___x_1783_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1776_, v___f_1782_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___boxed(lean_object* v_mvarId_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_mvarId_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(lean_object* v_msg_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = lean_box(0);
v___x_1793_ = lean_panic_fn_borrowed(v___x_1792_, v_msg_1791_);
return v___x_1793_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_1796_ = lean_unsigned_to_nat(30u);
v___x_1797_ = lean_unsigned_to_nat(150u);
v___x_1798_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__0));
v___x_1799_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_1800_ = l_mkPanicMessageWithDecl(v___x_1799_, v___x_1798_, v___x_1797_, v___x_1796_, v___x_1795_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(lean_object* v_fst_1801_, lean_object* v_snd_1802_, lean_object* v_fst_1803_, lean_object* v_fst_1804_, lean_object* v_00___1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1);
v___x_1812_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_1811_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1823_; 
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v___x_1812_, 0);
lean_dec(v_unused_1824_);
v___x_1814_ = v___x_1812_;
v_isShared_1815_ = v_isSharedCheck_1823_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v___x_1812_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1823_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v_fst_1801_);
lean_ctor_set(v___x_1816_, 1, v_snd_1802_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_fst_1803_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_fst_1804_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1819_);
v___x_1821_ = v___x_1814_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_fst_1804_);
lean_dec(v_fst_1803_);
lean_dec(v_snd_1802_);
lean_dec(v_fst_1801_);
v_a_1825_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1812_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1812_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___boxed(lean_object* v_fst_1833_, lean_object* v_snd_1834_, lean_object* v_fst_1835_, lean_object* v_fst_1836_, lean_object* v_00___1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1833_, v_snd_1834_, v_fst_1835_, v_fst_1836_, v_00___1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(lean_object* v_snd_1844_, lean_object* v_snd_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v_____r_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1854_ = l_Lean_Expr_mvarId_x21(v_snd_1844_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v_snd_1845_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1846_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1847_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1___boxed(lean_object* v_snd_1861_, lean_object* v_snd_1862_, lean_object* v___x_1863_, lean_object* v___x_1864_, lean_object* v_____r_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1861_, v_snd_1862_, v___x_1863_, v___x_1864_, v_____r_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v_snd_1861_);
return v_res_1871_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__0));
v___x_1874_ = l_Lean_stringToMessageData(v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(lean_object* v_upperBound_1875_, lean_object* v_args_1876_, lean_object* v___x_1877_, lean_object* v_origTag_1878_, lean_object* v_tacticName_1879_, lean_object* v_a_1880_, lean_object* v_b_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_a_1888_; lean_object* v___y_1893_; uint8_t v___x_1912_; 
v___x_1912_ = lean_nat_dec_lt(v_a_1880_, v_upperBound_1875_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_b_1881_);
return v___x_1913_;
}
else
{
lean_object* v_snd_1914_; lean_object* v_snd_1915_; lean_object* v_fst_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_2037_; 
v_snd_1914_ = lean_ctor_get(v_b_1881_, 1);
lean_inc(v_snd_1914_);
v_snd_1915_ = lean_ctor_get(v_snd_1914_, 1);
lean_inc(v_snd_1915_);
v_fst_1916_ = lean_ctor_get(v_b_1881_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_b_1881_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v_b_1881_, 1);
lean_dec(v_unused_2038_);
v___x_1918_ = v_b_1881_;
v_isShared_1919_ = v_isSharedCheck_2037_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_fst_1916_);
lean_dec(v_b_1881_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_2037_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_fst_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_2035_; 
v_fst_1920_ = lean_ctor_get(v_snd_1914_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_snd_1914_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_snd_1914_, 1);
lean_dec(v_unused_2036_);
v___x_1922_ = v_snd_1914_;
v_isShared_1923_ = v_isSharedCheck_2035_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_fst_1920_);
lean_dec(v_snd_1914_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_2035_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_fst_1924_; lean_object* v_snd_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_2034_; 
v_fst_1924_ = lean_ctor_get(v_snd_1915_, 0);
v_snd_1925_ = lean_ctor_get(v_snd_1915_, 1);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_snd_1915_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_1927_ = v_snd_1915_;
v_isShared_1928_ = v_isSharedCheck_2034_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_snd_1925_);
lean_inc(v_fst_1924_);
lean_dec(v_snd_1915_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_2034_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1929_ = l_Lean_instInhabitedExpr;
v___x_1930_ = lean_array_get_borrowed(v___x_1929_, v_args_1876_, v_a_1880_);
v___x_1931_ = lean_array_fget_borrowed(v___x_1877_, v_a_1880_);
v___x_1932_ = lean_unbox(v___x_1931_);
switch(v___x_1932_)
{
case 1:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
lean_del_object(v___x_1927_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
v___x_1933_ = lean_box(0);
v___x_1934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1924_, v_snd_1925_, v_fst_1920_, v_fst_1916_, v___x_1933_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
v___y_1893_ = v___x_1934_;
goto v___jp_1892_;
}
case 2:
{
lean_object* v___x_1935_; 
lean_del_object(v___x_1927_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_inc(v_origTag_1878_);
lean_inc(v___x_1930_);
v___x_1935_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_1930_, v_origTag_1878_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1964_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v_fst_1937_ = lean_ctor_get(v_a_1936_, 0);
v_snd_1938_ = lean_ctor_get(v_a_1936_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_a_1936_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1940_ = v_a_1936_;
v_isShared_1941_ = v_isSharedCheck_1964_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_snd_1938_);
lean_inc(v_fst_1937_);
lean_dec(v_a_1936_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1964_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_inc(v_fst_1937_);
v___x_1942_ = l_Lean_Expr_app___override(v_fst_1916_, v_fst_1937_);
lean_inc(v_snd_1938_);
lean_inc(v___x_1930_);
v___x_1943_ = l_Lean_mkApp3(v_fst_1920_, v___x_1930_, v_fst_1937_, v_snd_1938_);
if (lean_obj_tag(v_fst_1924_) == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_del_object(v___x_1940_);
v___x_1944_ = lean_box(0);
v___x_1945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1938_, v_snd_1925_, v___x_1943_, v___x_1942_, v___x_1944_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v_snd_1938_);
v___y_1893_ = v___x_1945_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1949_; 
lean_dec_ref_known(v_fst_1924_, 1);
v___x_1946_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
lean_inc_ref(v_tacticName_1879_);
v___x_1947_ = l_Lean_stringToMessageData(v_tacticName_1879_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set_tag(v___x_1940_, 7);
lean_ctor_set(v___x_1940_, 1, v___x_1947_);
lean_ctor_set(v___x_1940_, 0, v___x_1946_);
v___x_1949_ = v___x_1940_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1951_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1938_, v_snd_1925_, v___x_1943_, v___x_1942_, v_a_1953_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v_snd_1938_);
v___y_1893_ = v___x_1954_;
goto v___jp_1892_;
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec_ref(v___x_1943_);
lean_dec_ref(v___x_1942_);
lean_dec(v_snd_1938_);
lean_dec(v_snd_1925_);
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v_a_1955_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1952_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1952_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec(v_snd_1925_);
lean_dec(v_fst_1924_);
lean_dec(v_fst_1920_);
lean_dec(v_fst_1916_);
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v_a_1965_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1935_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1935_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
case 4:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_del_object(v___x_1927_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
v___x_1973_ = lean_box(0);
v___x_1974_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1924_, v_snd_1925_, v_fst_1920_, v_fst_1916_, v___x_1973_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
v___y_1893_ = v___x_1974_;
goto v___jp_1892_;
}
case 5:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_inc(v___x_1930_);
v___x_1975_ = l_Lean_Expr_app___override(v_fst_1920_, v___x_1930_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc_ref(v___x_1975_);
v___x_1976_ = lean_infer_type(v___x_1975_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
v___x_1978_ = lean_whnf(v_a_1977_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l_Lean_Expr_bindingDomain_x21(v_a_1979_);
lean_dec(v_a_1979_);
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
v___x_1982_ = 0;
v___x_1983_ = lean_box(0);
v___x_1984_ = l_Lean_Meta_mkFreshExprMVar(v___x_1981_, v___x_1982_, v___x_1983_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc_n(v_a_1985_, 3);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l_Lean_Expr_app___override(v_fst_1916_, v_a_1985_);
v___x_1987_ = l_Lean_Expr_app___override(v___x_1975_, v_a_1985_);
v___x_1988_ = l_Lean_Expr_mvarId_x21(v_a_1985_);
lean_dec(v_a_1985_);
v___x_1989_ = lean_array_push(v_snd_1925_, v___x_1988_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___x_1989_);
v___x_1991_ = v___x_1927_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_fst_1924_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1991_);
lean_ctor_set(v___x_1922_, 0, v___x_1987_);
v___x_1993_ = v___x_1922_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1995_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1993_);
lean_ctor_set(v___x_1918_, 0, v___x_1986_);
v___x_1995_ = v___x_1918_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
v_a_1888_ = v___x_1995_;
goto v___jp_1887_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v___x_1975_);
lean_del_object(v___x_1927_);
lean_dec(v_snd_1925_);
lean_dec(v_fst_1924_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1916_);
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v_a_1999_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1984_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1984_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
lean_dec_ref(v___x_1975_);
lean_del_object(v___x_1927_);
lean_dec(v_snd_1925_);
lean_dec(v_fst_1924_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1916_);
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v_a_2007_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_1978_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_dec(v___x_1978_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_a_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec_ref(v___x_1975_);
lean_del_object(v___x_1927_);
lean_dec(v_snd_1925_);
lean_dec(v_fst_1924_);
lean_del_object(v___x_1922_);
lean_del_object(v___x_1918_);
lean_dec(v_fst_1916_);
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v_a_2015_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1976_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1976_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
default: 
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_inc_n(v___x_1930_, 2);
v___x_2023_ = l_Lean_Expr_app___override(v_fst_1916_, v___x_1930_);
v___x_2024_ = l_Lean_Expr_app___override(v_fst_1920_, v___x_1930_);
if (v_isShared_1928_ == 0)
{
v___x_2026_ = v___x_1927_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_fst_1924_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_snd_1925_);
v___x_2026_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_2026_);
lean_ctor_set(v___x_1922_, 0, v___x_2024_);
v___x_2028_ = v___x_1922_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_2028_);
lean_ctor_set(v___x_1918_, 0, v___x_2023_);
v___x_2030_ = v___x_1918_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
v_a_1888_ = v___x_2030_;
goto v___jp_1887_;
}
}
}
}
}
}
}
}
}
v___jp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_unsigned_to_nat(1u);
v___x_1890_ = lean_nat_add(v_a_1880_, v___x_1889_);
lean_dec(v_a_1880_);
v_a_1880_ = v___x_1890_;
v_b_1881_ = v_a_1888_;
goto _start;
}
v___jp_1892_:
{
if (lean_obj_tag(v___y_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1903_; 
v_a_1894_ = lean_ctor_get(v___y_1893_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___y_1893_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1896_ = v___y_1893_;
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___y_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1903_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
if (lean_obj_tag(v_a_1894_) == 0)
{
lean_object* v_a_1898_; lean_object* v___x_1900_; 
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v_a_1898_ = lean_ctor_get(v_a_1894_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v_a_1894_, 1);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v_a_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v_a_1902_; 
lean_del_object(v___x_1896_);
v_a_1902_ = lean_ctor_get(v_a_1894_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v_a_1894_, 1);
v_a_1888_ = v_a_1902_;
goto v___jp_1887_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1880_);
lean_dec_ref(v_tacticName_1879_);
lean_dec(v_origTag_1878_);
v_a_1904_ = lean_ctor_get(v___y_1893_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___y_1893_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___y_1893_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___y_1893_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___boxed(lean_object* v_upperBound_2039_, lean_object* v_args_2040_, lean_object* v___x_2041_, lean_object* v_origTag_2042_, lean_object* v_tacticName_2043_, lean_object* v_a_2044_, lean_object* v_b_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2039_, v_args_2040_, v___x_2041_, v_origTag_2042_, v_tacticName_2043_, v_a_2044_, v_b_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec_ref(v___x_2041_);
lean_dec_ref(v_args_2040_);
lean_dec(v_upperBound_2039_);
return v_res_2051_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2));
v___x_2056_ = lean_unsigned_to_nat(14u);
v___x_2057_ = lean_unsigned_to_nat(22u);
v___x_2058_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1));
v___x_2059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0));
v___x_2060_ = l_mkPanicMessageWithDecl(v___x_2059_, v___x_2058_, v___x_2057_, v___x_2056_, v___x_2055_);
return v___x_2060_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5));
v___x_2066_ = l_Lean_stringToMessageData(v___x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(lean_object* v_tacticName_2067_, lean_object* v_origTag_2068_, lean_object* v_f_2069_, lean_object* v_args_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v_lower_2091_; lean_object* v_upper_2092_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = 0;
v___x_2109_ = lean_array_get_size(v_args_2070_);
lean_inc_ref(v_f_2069_);
v___x_2110_ = l_Lean_Meta_getFunInfoNArgs(v_f_2069_, v___x_2109_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_a_2111_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = 0;
lean_inc_ref(v_f_2069_);
v___x_2115_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_2069_, v_a_2111_, v_a_2113_, v___x_2114_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2117_; lean_object* v_proof_2118_; lean_object* v_argKinds_2119_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v_val_2117_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_val_2117_);
lean_dec_ref_known(v_a_2116_, 1);
v_proof_2118_ = lean_ctor_get(v_val_2117_, 1);
lean_inc_ref(v_proof_2118_);
v_argKinds_2119_ = lean_ctor_get(v_val_2117_, 2);
lean_inc_ref(v_argKinds_2119_);
lean_dec(v_val_2117_);
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = lean_box(v___x_2108_);
v___x_2148_ = lean_array_get(v___x_2147_, v_argKinds_2119_, v___x_2146_);
lean_dec(v___x_2147_);
v___x_2149_ = lean_unbox(v___x_2148_);
lean_dec(v___x_2148_);
if (v___x_2149_ == 2)
{
v___y_2121_ = v_a_2071_;
v___y_2122_ = v_a_2072_;
v___y_2123_ = v_a_2073_;
v___y_2124_ = v_a_2074_;
goto v___jp_2120_;
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v_argKinds_2119_);
lean_dec_ref(v_proof_2118_);
lean_dec_ref(v_args_2070_);
lean_dec_ref(v_f_2069_);
lean_dec(v_origTag_2068_);
v___x_2150_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2151_ = l_Lean_stringToMessageData(v_tacticName_2067_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2154_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
v___jp_2120_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2125_ = lean_array_get_size(v_argKinds_2119_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4));
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v_proof_2118_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_f_2069_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v___x_2125_, v_args_2070_, v_argKinds_2119_, v_origTag_2068_, v_tacticName_2067_, v___x_2126_, v___x_2129_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec_ref(v_argKinds_2119_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v_snd_2132_; lean_object* v_snd_2133_; lean_object* v_fst_2134_; lean_object* v_fst_2135_; lean_object* v_snd_2136_; uint8_t v___x_2137_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v_snd_2132_ = lean_ctor_get(v_a_2131_, 1);
lean_inc(v_snd_2132_);
lean_dec(v_a_2131_);
v_snd_2133_ = lean_ctor_get(v_snd_2132_, 1);
lean_inc(v_snd_2133_);
v_fst_2134_ = lean_ctor_get(v_snd_2132_, 0);
lean_inc(v_fst_2134_);
lean_dec(v_snd_2132_);
v_fst_2135_ = lean_ctor_get(v_snd_2133_, 0);
lean_inc(v_fst_2135_);
v_snd_2136_ = lean_ctor_get(v_snd_2133_, 1);
lean_inc(v_snd_2136_);
lean_dec(v_snd_2133_);
v___x_2137_ = lean_nat_dec_le(v___x_2125_, v___x_2126_);
if (v___x_2137_ == 0)
{
v___y_2084_ = v_fst_2135_;
v___y_2085_ = v___y_2122_;
v___y_2086_ = v___y_2124_;
v___y_2087_ = v_snd_2136_;
v___y_2088_ = v___y_2121_;
v___y_2089_ = v_fst_2134_;
v___y_2090_ = v___y_2123_;
v_lower_2091_ = v___x_2125_;
v_upper_2092_ = v___x_2109_;
goto v___jp_2083_;
}
else
{
v___y_2084_ = v_fst_2135_;
v___y_2085_ = v___y_2122_;
v___y_2086_ = v___y_2124_;
v___y_2087_ = v_snd_2136_;
v___y_2088_ = v___y_2121_;
v___y_2089_ = v_fst_2134_;
v___y_2090_ = v___y_2123_;
v_lower_2091_ = v___x_2126_;
v_upper_2092_ = v___x_2109_;
goto v___jp_2083_;
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_args_2070_);
v_a_2138_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2130_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2130_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v_a_2116_);
lean_dec_ref(v_args_2070_);
lean_dec_ref(v_f_2069_);
lean_dec(v_origTag_2068_);
v___x_2164_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2165_ = l_Lean_stringToMessageData(v_tacticName_2067_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2168_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
return v___x_2169_;
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_args_2070_);
lean_dec_ref(v_f_2069_);
lean_dec(v_origTag_2068_);
lean_dec_ref(v_tacticName_2067_);
v_a_2170_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2115_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2115_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_a_2111_);
lean_dec_ref(v_args_2070_);
lean_dec_ref(v_f_2069_);
lean_dec(v_origTag_2068_);
lean_dec_ref(v_tacticName_2067_);
v_a_2178_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2112_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2112_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec_ref(v_args_2070_);
lean_dec_ref(v_f_2069_);
lean_dec(v_origTag_2068_);
lean_dec_ref(v_tacticName_2067_);
v_a_2186_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2110_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2110_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
v___jp_2076_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___y_2079_);
lean_ctor_set(v___x_2080_, 1, v___y_2078_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___y_2077_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
v___jp_2083_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = l_Array_toSubarray___redArg(v_args_2070_, v_lower_2091_, v_upper_2092_);
v___x_2094_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_2093_, v___y_2089_, v___y_2088_, v___y_2085_, v___y_2090_, v___y_2086_);
if (lean_obj_tag(v___x_2094_) == 0)
{
if (lean_obj_tag(v___y_2084_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3);
v___x_2097_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(v___x_2096_);
v___y_2077_ = v_a_2095_;
v___y_2078_ = v___y_2087_;
v___y_2079_ = v___x_2097_;
goto v___jp_2076_;
}
else
{
lean_object* v_a_2098_; lean_object* v_val_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2094_, 1);
v_val_2099_ = lean_ctor_get(v___y_2084_, 0);
lean_inc(v_val_2099_);
lean_dec_ref_known(v___y_2084_, 1);
v___y_2077_ = v_a_2098_;
v___y_2078_ = v___y_2087_;
v___y_2079_ = v_val_2099_;
goto v___jp_2076_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v___y_2087_);
lean_dec(v___y_2084_);
v_a_2100_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2094_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2094_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___boxed(lean_object* v_tacticName_2194_, lean_object* v_origTag_2195_, lean_object* v_f_2196_, lean_object* v_args_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_2194_, v_origTag_2195_, v_f_2196_, v_args_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(lean_object* v_upperBound_2204_, lean_object* v_args_2205_, lean_object* v___x_2206_, lean_object* v_origTag_2207_, lean_object* v_tacticName_2208_, lean_object* v_inst_2209_, lean_object* v_R_2210_, lean_object* v_a_2211_, lean_object* v_b_2212_, lean_object* v_c_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2204_, v_args_2205_, v___x_2206_, v_origTag_2207_, v_tacticName_2208_, v_a_2211_, v_b_2212_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___boxed(lean_object* v_upperBound_2220_, lean_object* v_args_2221_, lean_object* v___x_2222_, lean_object* v_origTag_2223_, lean_object* v_tacticName_2224_, lean_object* v_inst_2225_, lean_object* v_R_2226_, lean_object* v_a_2227_, lean_object* v_b_2228_, lean_object* v_c_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(v_upperBound_2220_, v_args_2221_, v___x_2222_, v_origTag_2223_, v_tacticName_2224_, v_inst_2225_, v_R_2226_, v_a_2227_, v_b_2228_, v_c_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___x_2222_);
lean_dec_ref(v_args_2221_);
lean_dec(v_upperBound_2220_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(lean_object* v_msg_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___f_2242_; lean_object* v___x_3702__overap_2243_; lean_object* v___x_2244_; 
v___f_2242_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_3702__overap_2243_ = lean_panic_fn_borrowed(v___f_2242_, v_msg_2236_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
v___x_2244_ = lean_apply_5(v___x_3702__overap_2243_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, lean_box(0));
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1___boxed(lean_object* v_msg_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v_msg_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(lean_object* v_binderType_2255_, lean_object* v_body_2256_, lean_object* v_mvarId_2257_, uint8_t v_domain_2258_, uint8_t v___x_2259_, lean_object* v_binderName_2260_, lean_object* v_tacticName_2261_, lean_object* v_rhs_2262_, lean_object* v_arg_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___x_2269_; 
lean_inc_ref(v_binderType_2255_);
v___x_2269_ = l_Lean_Meta_getLevel(v_binderType_2255_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = lean_expr_instantiate1(v_body_2256_, v_arg_2263_);
lean_inc(v_mvarId_2257_);
v___x_2272_ = l_Lean_MVarId_getTag(v_mvarId_2257_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref_known(v___x_2272_, 1);
lean_inc_ref(v___x_2271_);
v___x_2274_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_2271_, v_a_2273_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v_fst_2276_; lean_object* v_snd_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2351_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_a_2275_);
lean_dec_ref_known(v___x_2274_, 1);
v_fst_2276_ = lean_ctor_get(v_a_2275_, 0);
v_snd_2277_ = lean_ctor_get(v_a_2275_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_a_2275_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2279_ = v_a_2275_;
v_isShared_2280_ = v_isSharedCheck_2351_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_snd_2277_);
lean_inc(v_fst_2276_);
lean_dec(v_a_2275_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2351_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_Meta_getLevel(v___x_2271_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_mk_empty_array_with_capacity(v___x_2283_);
v___x_2285_ = lean_array_push(v___x_2284_, v_arg_2263_);
v___x_2286_ = 1;
v___x_2287_ = l_Lean_Meta_mkLambdaFVars(v___x_2285_, v_fst_2276_, v_domain_2258_, v___x_2259_, v_domain_2258_, v___x_2259_, v___x_2286_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
lean_inc(v_snd_2277_);
v___x_2289_ = l_Lean_Meta_mkLambdaFVars(v___x_2285_, v_snd_2277_, v_domain_2258_, v___x_2259_, v_domain_2258_, v___x_2259_, v___x_2286_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec_ref(v___x_2285_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v___x_2291_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1));
v___x_2292_ = lean_box(0);
if (v_isShared_2280_ == 0)
{
lean_ctor_set_tag(v___x_2279_, 1);
lean_ctor_set(v___x_2279_, 1, v___x_2292_);
lean_ctor_set(v___x_2279_, 0, v_a_2282_);
v___x_2294_ = v___x_2279_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2282_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_a_2270_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = l_Lean_Expr_const___override(v___x_2291_, v___x_2295_);
v___x_2297_ = 0;
lean_inc_ref(v_binderType_2255_);
v___x_2298_ = l_Lean_Expr_lam___override(v_binderName_2260_, v_binderType_2255_, v_body_2256_, v___x_2297_);
v___x_2299_ = lean_unsigned_to_nat(4u);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
v___x_2301_ = lean_array_push(v___x_2300_, v_binderType_2255_);
v___x_2302_ = lean_array_push(v___x_2301_, v___x_2298_);
v___x_2303_ = lean_array_push(v___x_2302_, v_a_2288_);
v___x_2304_ = lean_array_push(v___x_2303_, v_a_2290_);
v___x_2305_ = l_Lean_mkAppN(v___x_2296_, v___x_2304_);
lean_dec_ref(v___x_2304_);
lean_inc_ref(v___x_2305_);
v___x_2306_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2261_, v_rhs_2262_, v___x_2305_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref_known(v___x_2306_, 1);
v___x_2307_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2257_, v___x_2305_, v___y_2265_);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v___x_2307_, 0);
lean_dec(v_unused_2317_);
v___x_2309_ = v___x_2307_;
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
else
{
lean_dec(v___x_2307_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = l_Lean_Expr_mvarId_x21(v_snd_2277_);
lean_dec(v_snd_2277_);
v___x_2312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2292_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2312_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v___x_2305_);
lean_dec(v_snd_2277_);
lean_dec(v_mvarId_2257_);
v_a_2318_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2306_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2306_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_a_2288_);
lean_dec(v_a_2282_);
lean_del_object(v___x_2279_);
lean_dec(v_snd_2277_);
lean_dec(v_a_2270_);
lean_dec_ref(v_rhs_2262_);
lean_dec_ref(v_tacticName_2261_);
lean_dec(v_binderName_2260_);
lean_dec(v_mvarId_2257_);
lean_dec_ref(v_body_2256_);
lean_dec_ref(v_binderType_2255_);
v_a_2327_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2289_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2289_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___x_2285_);
lean_dec(v_a_2282_);
lean_del_object(v___x_2279_);
lean_dec(v_snd_2277_);
lean_dec(v_a_2270_);
lean_dec_ref(v_rhs_2262_);
lean_dec_ref(v_tacticName_2261_);
lean_dec(v_binderName_2260_);
lean_dec(v_mvarId_2257_);
lean_dec_ref(v_body_2256_);
lean_dec_ref(v_binderType_2255_);
v_a_2335_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2287_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2287_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_del_object(v___x_2279_);
lean_dec(v_snd_2277_);
lean_dec(v_fst_2276_);
lean_dec(v_a_2270_);
lean_dec_ref(v_arg_2263_);
lean_dec_ref(v_rhs_2262_);
lean_dec_ref(v_tacticName_2261_);
lean_dec(v_binderName_2260_);
lean_dec(v_mvarId_2257_);
lean_dec_ref(v_body_2256_);
lean_dec_ref(v_binderType_2255_);
v_a_2343_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2281_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2281_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v___x_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_arg_2263_);
lean_dec_ref(v_rhs_2262_);
lean_dec_ref(v_tacticName_2261_);
lean_dec(v_binderName_2260_);
lean_dec(v_mvarId_2257_);
lean_dec_ref(v_body_2256_);
lean_dec_ref(v_binderType_2255_);
v_a_2352_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2274_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2274_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v___x_2271_);
lean_dec(v_a_2270_);
lean_dec_ref(v_arg_2263_);
lean_dec_ref(v_rhs_2262_);
lean_dec_ref(v_tacticName_2261_);
lean_dec(v_binderName_2260_);
lean_dec(v_mvarId_2257_);
lean_dec_ref(v_body_2256_);
lean_dec_ref(v_binderType_2255_);
v_a_2360_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2272_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2272_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v_arg_2263_);
lean_dec_ref(v_rhs_2262_);
lean_dec_ref(v_tacticName_2261_);
lean_dec(v_binderName_2260_);
lean_dec(v_mvarId_2257_);
lean_dec_ref(v_body_2256_);
lean_dec_ref(v_binderType_2255_);
v_a_2368_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2269_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2269_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed(lean_object* v_binderType_2376_, lean_object* v_body_2377_, lean_object* v_mvarId_2378_, lean_object* v_domain_2379_, lean_object* v___x_2380_, lean_object* v_binderName_2381_, lean_object* v_tacticName_2382_, lean_object* v_rhs_2383_, lean_object* v_arg_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
uint8_t v_domain_boxed_2390_; uint8_t v___x_4129__boxed_2391_; lean_object* v_res_2392_; 
v_domain_boxed_2390_ = lean_unbox(v_domain_2379_);
v___x_4129__boxed_2391_ = lean_unbox(v___x_2380_);
v_res_2392_ = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(v_binderType_2376_, v_body_2377_, v_mvarId_2378_, v_domain_boxed_2390_, v___x_4129__boxed_2391_, v_binderName_2381_, v_tacticName_2382_, v_rhs_2383_, v_arg_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2393_, lean_object* v_b_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; 
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
lean_inc(v___y_2396_);
lean_inc_ref(v___y_2395_);
v___x_2400_ = lean_apply_6(v_k_2393_, v_b_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, lean_box(0));
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(v_k_2401_, v_b_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(lean_object* v_name_2409_, uint8_t v_bi_2410_, lean_object* v_type_2411_, lean_object* v_k_2412_, uint8_t v_kind_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___f_2419_; lean_object* v___x_2420_; 
v___f_2419_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2419_, 0, v_k_2412_);
v___x_2420_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2409_, v_bi_2410_, v_type_2411_, v___f_2419_, v_kind_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2420_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2420_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_2437_, lean_object* v_bi_2438_, lean_object* v_type_2439_, lean_object* v_k_2440_, lean_object* v_kind_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v_bi_boxed_2447_; uint8_t v_kind_boxed_2448_; lean_object* v_res_2449_; 
v_bi_boxed_2447_ = lean_unbox(v_bi_2438_);
v_kind_boxed_2448_ = lean_unbox(v_kind_2441_);
v_res_2449_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2437_, v_bi_boxed_2447_, v_type_2439_, v_k_2440_, v_kind_boxed_2448_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(lean_object* v_name_2450_, lean_object* v_type_2451_, lean_object* v_k_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
uint8_t v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = 0;
v___x_2459_ = 0;
v___x_2460_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2450_, v___x_2458_, v_type_2451_, v_k_2452_, v___x_2459_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg___boxed(lean_object* v_name_2461_, lean_object* v_type_2462_, lean_object* v_k_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2461_, v_type_2462_, v_k_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2469_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0));
v___x_2472_ = l_Lean_stringToMessageData(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2477_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_2478_ = lean_unsigned_to_nat(33u);
v___x_2479_ = lean_unsigned_to_nat(158u);
v___x_2480_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4));
v___x_2481_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_2482_ = l_mkPanicMessageWithDecl(v___x_2481_, v___x_2480_, v___x_2479_, v___x_2478_, v___x_2477_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall(lean_object* v_tacticName_2483_, uint8_t v_domain_2484_, lean_object* v_mvarId_2485_, lean_object* v_lhs_2486_, lean_object* v_rhs_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
if (lean_obj_tag(v_lhs_2486_) == 7)
{
lean_object* v_binderName_2493_; lean_object* v_binderType_2494_; lean_object* v_body_2495_; uint8_t v_binderInfo_2496_; lean_object* v___y_2498_; 
v_binderName_2493_ = lean_ctor_get(v_lhs_2486_, 0);
lean_inc(v_binderName_2493_);
v_binderType_2494_ = lean_ctor_get(v_lhs_2486_, 1);
lean_inc_ref(v_binderType_2494_);
v_body_2495_ = lean_ctor_get(v_lhs_2486_, 2);
lean_inc_ref(v_body_2495_);
v_binderInfo_2496_ = lean_ctor_get_uint8(v_lhs_2486_, sizeof(void*)*3 + 8);
if (v_domain_2484_ == 0)
{
uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; 
lean_dec_ref_known(v_lhs_2486_, 3);
v___x_2581_ = 1;
v___x_2582_ = lean_box(v_domain_2484_);
v___x_2583_ = lean_box(v___x_2581_);
lean_inc(v_binderName_2493_);
lean_inc_ref(v_binderType_2494_);
v___f_2584_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed), 14, 8);
lean_closure_set(v___f_2584_, 0, v_binderType_2494_);
lean_closure_set(v___f_2584_, 1, v_body_2495_);
lean_closure_set(v___f_2584_, 2, v_mvarId_2485_);
lean_closure_set(v___f_2584_, 3, v___x_2582_);
lean_closure_set(v___f_2584_, 4, v___x_2583_);
lean_closure_set(v___f_2584_, 5, v_binderName_2493_);
lean_closure_set(v___f_2584_, 6, v_tacticName_2483_);
lean_closure_set(v___f_2584_, 7, v_rhs_2487_);
v___x_2585_ = l_Lean_Core_mkFreshUserName(v_binderName_2493_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2587_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v___x_2587_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_a_2586_, v_binderType_2494_, v___f_2584_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
return v___x_2587_;
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v___f_2584_);
lean_dec_ref(v_binderType_2494_);
v_a_2588_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2585_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2585_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
uint8_t v___x_2596_; 
v___x_2596_ = l_Lean_Expr_hasLooseBVars(v_body_2495_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; 
lean_dec_ref_known(v_lhs_2486_, 3);
lean_inc(v_mvarId_2485_);
v___x_2597_ = l_Lean_MVarId_getTag(v_mvarId_2485_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2494_, v_a_2598_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2655_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_fst_2601_ = lean_ctor_get(v_a_2600_, 0);
v_snd_2602_ = lean_ctor_get(v_a_2600_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_a_2600_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2604_ = v_a_2600_;
v_isShared_2605_ = v_isSharedCheck_2655_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snd_2602_);
lean_inc(v_fst_2601_);
lean_dec(v_a_2600_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2655_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; 
lean_inc_ref(v_body_2495_);
v___x_2606_ = l_Lean_Meta_mkEqRefl(v_body_2495_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3));
v___x_2609_ = lean_unsigned_to_nat(2u);
v___x_2610_ = lean_mk_empty_array_with_capacity(v___x_2609_);
lean_inc(v_snd_2602_);
v___x_2611_ = lean_array_push(v___x_2610_, v_snd_2602_);
v___x_2612_ = lean_array_push(v___x_2611_, v_a_2607_);
v___x_2613_ = l_Lean_Meta_mkAppM(v___x_2608_, v___x_2612_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v___x_2615_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2485_, v_a_2614_, v_a_2489_);
lean_dec_ref(v___x_2615_);
v___x_2616_ = l_Lean_Expr_forallE___override(v_binderName_2493_, v_fst_2601_, v_body_2495_, v_binderInfo_2496_);
v___x_2617_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_2483_, v_rhs_2487_, v___x_2616_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2629_; 
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v___x_2617_, 0);
lean_dec(v_unused_2630_);
v___x_2619_ = v___x_2617_;
v_isShared_2620_ = v_isSharedCheck_2629_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v___x_2617_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2629_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2621_ = l_Lean_Expr_mvarId_x21(v_snd_2602_);
lean_dec(v_snd_2602_);
v___x_2622_ = lean_box(0);
if (v_isShared_2605_ == 0)
{
lean_ctor_set_tag(v___x_2604_, 1);
lean_ctor_set(v___x_2604_, 1, v___x_2622_);
lean_ctor_set(v___x_2604_, 0, v___x_2621_);
v___x_2624_ = v___x_2604_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2624_);
v___x_2626_ = v___x_2619_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_del_object(v___x_2604_);
lean_dec(v_snd_2602_);
v_a_2631_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2617_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2617_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_del_object(v___x_2604_);
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_dec_ref(v_body_2495_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2639_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2613_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2613_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_del_object(v___x_2604_);
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_dec_ref(v_body_2495_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2647_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2606_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2606_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref(v_body_2495_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2656_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2599_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2599_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v_body_2495_);
lean_dec_ref(v_binderType_2494_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2664_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2597_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2597_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v___x_2672_; 
lean_inc_ref(v_body_2495_);
v___x_2672_ = l_Lean_Meta_isProp(v_body_2495_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; uint8_t v___x_2674_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v___x_2674_ = lean_unbox(v_a_2673_);
if (v___x_2674_ == 0)
{
lean_dec_ref_known(v_lhs_2486_, 3);
v___y_2498_ = v___x_2672_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2675_; 
lean_dec_ref_known(v___x_2672_, 1);
v___x_2675_ = l_Lean_Meta_isProp(v_lhs_2486_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
v___y_2498_ = v___x_2675_;
goto v___jp_2497_;
}
}
else
{
lean_dec_ref_known(v_lhs_2486_, 3);
v___y_2498_ = v___x_2672_;
goto v___jp_2497_;
}
}
}
v___jp_2497_:
{
if (lean_obj_tag(v___y_2498_) == 0)
{
lean_object* v_a_2499_; uint8_t v___x_2500_; 
v_a_2499_ = lean_ctor_get(v___y_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___y_2498_, 1);
v___x_2500_ = lean_unbox(v_a_2499_);
lean_dec(v_a_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_body_2495_);
lean_dec_ref(v_binderType_2494_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
v___x_2501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2502_ = l_Lean_stringToMessageData(v_tacticName_2483_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2505_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; 
lean_inc(v_mvarId_2485_);
v___x_2507_ = l_Lean_MVarId_getTag(v_mvarId_2485_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2509_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
lean_inc_ref(v_binderType_2494_);
v___x_2509_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2494_, v_a_2508_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v_snd_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2555_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2509_, 1);
v_snd_2511_ = lean_ctor_get(v_a_2510_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_a_2510_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v_a_2510_, 0);
lean_dec(v_unused_2556_);
v___x_2513_ = v_a_2510_;
v_isShared_2514_ = v_isSharedCheck_2555_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_snd_2511_);
lean_dec(v_a_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2555_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3));
v___x_2516_ = 0;
v___x_2517_ = l_Lean_Expr_lam___override(v_binderName_2493_, v_binderType_2494_, v_body_2495_, v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(2u);
v___x_2519_ = lean_mk_empty_array_with_capacity(v___x_2518_);
lean_inc(v_snd_2511_);
v___x_2520_ = lean_array_push(v___x_2519_, v_snd_2511_);
v___x_2521_ = lean_array_push(v___x_2520_, v___x_2517_);
v___x_2522_ = l_Lean_Meta_mkAppM(v___x_2515_, v___x_2521_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_n(v_a_2523_, 2);
lean_dec_ref_known(v___x_2522_, 1);
v___x_2524_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2483_, v_rhs_2487_, v_a_2523_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v___x_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref_known(v___x_2524_, 1);
v___x_2525_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2485_, v_a_2523_, v_a_2489_);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v___x_2525_, 0);
lean_dec(v_unused_2538_);
v___x_2527_ = v___x_2525_;
v_isShared_2528_ = v_isSharedCheck_2537_;
goto v_resetjp_2526_;
}
else
{
lean_dec(v___x_2525_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2537_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
v___x_2529_ = l_Lean_Expr_mvarId_x21(v_snd_2511_);
lean_dec(v_snd_2511_);
v___x_2530_ = lean_box(0);
if (v_isShared_2514_ == 0)
{
lean_ctor_set_tag(v___x_2513_, 1);
lean_ctor_set(v___x_2513_, 1, v___x_2530_);
lean_ctor_set(v___x_2513_, 0, v___x_2529_);
v___x_2532_ = v___x_2513_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2529_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
lean_object* v___x_2534_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2532_);
v___x_2534_ = v___x_2527_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2523_);
lean_del_object(v___x_2513_);
lean_dec(v_snd_2511_);
lean_dec(v_mvarId_2485_);
v_a_2539_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2524_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2524_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_del_object(v___x_2513_);
lean_dec(v_snd_2511_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2547_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2522_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2522_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_body_2495_);
lean_dec_ref(v_binderType_2494_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2557_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2509_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2509_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_body_2495_);
lean_dec_ref(v_binderType_2494_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2565_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2507_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2507_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec_ref(v_body_2495_);
lean_dec_ref(v_binderType_2494_);
lean_dec(v_binderName_2493_);
lean_dec_ref(v_rhs_2487_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v_a_2573_ = lean_ctor_get(v___y_2498_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___y_2498_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___y_2498_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___y_2498_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
lean_dec_ref(v_rhs_2487_);
lean_dec_ref(v_lhs_2486_);
lean_dec(v_mvarId_2485_);
lean_dec_ref(v_tacticName_2483_);
v___x_2676_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5);
v___x_2677_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v___x_2676_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___boxed(lean_object* v_tacticName_2678_, lean_object* v_domain_2679_, lean_object* v_mvarId_2680_, lean_object* v_lhs_2681_, lean_object* v_rhs_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
uint8_t v_domain_boxed_2688_; lean_object* v_res_2689_; 
v_domain_boxed_2688_ = lean_unbox(v_domain_2679_);
v_res_2689_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_2678_, v_domain_boxed_2688_, v_mvarId_2680_, v_lhs_2681_, v_rhs_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_object* v_00_u03b1_2690_, lean_object* v_name_2691_, uint8_t v_bi_2692_, lean_object* v_type_2693_, lean_object* v_k_2694_, uint8_t v_kind_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2691_, v_bi_2692_, v_type_2693_, v_k_2694_, v_kind_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2702_, lean_object* v_name_2703_, lean_object* v_bi_2704_, lean_object* v_type_2705_, lean_object* v_k_2706_, lean_object* v_kind_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
uint8_t v_bi_boxed_2713_; uint8_t v_kind_boxed_2714_; lean_object* v_res_2715_; 
v_bi_boxed_2713_ = lean_unbox(v_bi_2704_);
v_kind_boxed_2714_ = lean_unbox(v_kind_2707_);
v_res_2715_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(v_00_u03b1_2702_, v_name_2703_, v_bi_boxed_2713_, v_type_2705_, v_k_2706_, v_kind_boxed_2714_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_object* v_00_u03b1_2716_, lean_object* v_name_2717_, lean_object* v_type_2718_, lean_object* v_k_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2717_, v_type_2718_, v_k_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_name_2727_, lean_object* v_type_2728_, lean_object* v_k_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(v_00_u03b1_2726_, v_name_2727_, v_type_2728_, v_k_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__0(lean_object* v_a_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_nat_to_int(v_a_2736_);
return v___x_2737_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0));
v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(lean_object* v_snd_2741_, lean_object* v_a_2742_, lean_object* v_____r_2743_, lean_object* v_fType_2744_, lean_object* v_j_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
if (lean_obj_tag(v_fType_2744_) == 7)
{
lean_object* v_body_2751_; uint8_t v_binderInfo_2752_; uint8_t v___x_2753_; 
v_body_2751_ = lean_ctor_get(v_fType_2744_, 2);
lean_inc_ref(v_body_2751_);
v_binderInfo_2752_ = lean_ctor_get_uint8(v_fType_2744_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fType_2744_, 3);
v___x_2753_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_dec(v_a_2742_);
lean_inc(v_j_2745_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_j_2745_);
lean_ctor_set(v___x_2754_, 1, v_snd_2741_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_body_2751_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
return v___x_2757_;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2758_ = lean_array_push(v_snd_2741_, v_a_2742_);
lean_inc(v_j_2745_);
v___x_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2759_, 0, v_j_2745_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v_body_2751_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2760_);
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
return v___x_2762_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v_a_2742_);
v___x_2763_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1);
v___x_2764_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2763_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2774_; 
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2774_ == 0)
{
lean_object* v_unused_2775_; 
v_unused_2775_ = lean_ctor_get(v___x_2764_, 0);
lean_dec(v_unused_2775_);
v___x_2766_ = v___x_2764_;
v_isShared_2767_ = v_isSharedCheck_2774_;
goto v_resetjp_2765_;
}
else
{
lean_dec(v___x_2764_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2774_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_inc(v_j_2745_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_j_2745_);
lean_ctor_set(v___x_2768_, 1, v_snd_2741_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v_fType_2744_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2770_);
v___x_2772_ = v___x_2766_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec_ref(v_fType_2744_);
lean_dec(v_snd_2741_);
v_a_2776_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2764_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2764_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___boxed(lean_object* v_snd_2784_, lean_object* v_a_2785_, lean_object* v_____r_2786_, lean_object* v_fType_2787_, lean_object* v_j_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2784_, v_a_2785_, v_____r_2786_, v_fType_2787_, v_j_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v_j_2788_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(lean_object* v_upperBound_2795_, lean_object* v_xs_2796_, lean_object* v_a_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___y_2805_; uint8_t v___x_2827_; 
v___x_2827_ = lean_nat_dec_lt(v_a_2797_, v_upperBound_2795_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; 
lean_dec(v_a_2797_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_b_2798_);
return v___x_2828_;
}
else
{
lean_object* v_snd_2829_; lean_object* v_fst_2830_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v___y_2834_; uint8_t v___x_2846_; 
v_snd_2829_ = lean_ctor_get(v_b_2798_, 1);
lean_inc(v_snd_2829_);
v_fst_2830_ = lean_ctor_get(v_b_2798_, 0);
lean_inc(v_fst_2830_);
lean_dec_ref(v_b_2798_);
v_fst_2831_ = lean_ctor_get(v_snd_2829_, 0);
lean_inc(v_fst_2831_);
v_snd_2832_ = lean_ctor_get(v_snd_2829_, 1);
lean_inc(v_snd_2832_);
lean_dec(v_snd_2829_);
v___x_2846_ = l_Lean_Expr_isForall(v_fst_2830_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; uint8_t v_transparency_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2847_ = l_Lean_Meta_Context_config(v___y_2799_);
v_transparency_2848_ = lean_ctor_get_uint8(v___x_2847_, 9);
lean_dec_ref(v___x_2847_);
v___x_2849_ = 0;
v___x_2850_ = lean_expr_instantiate_rev_range(v_fst_2830_, v_fst_2831_, v_a_2797_, v_xs_2796_);
lean_dec(v_fst_2831_);
lean_dec(v_fst_2830_);
v___x_2851_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2848_, v___x_2849_);
if (v___x_2851_ == 0)
{
lean_object* v_keyedConfig_2852_; uint8_t v_trackZetaDelta_2853_; lean_object* v_zetaDeltaSet_2854_; lean_object* v_lctx_2855_; lean_object* v_localInstances_2856_; lean_object* v_defEqCtx_x3f_2857_; lean_object* v_synthPendingDepth_2858_; lean_object* v_customCanUnfoldPredicate_x3f_2859_; uint8_t v_univApprox_2860_; uint8_t v_inTypeClassResolution_2861_; uint8_t v_cacheInferType_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_keyedConfig_2852_ = lean_ctor_get(v___y_2799_, 0);
v_trackZetaDelta_2853_ = lean_ctor_get_uint8(v___y_2799_, sizeof(void*)*7);
v_zetaDeltaSet_2854_ = lean_ctor_get(v___y_2799_, 1);
v_lctx_2855_ = lean_ctor_get(v___y_2799_, 2);
v_localInstances_2856_ = lean_ctor_get(v___y_2799_, 3);
v_defEqCtx_x3f_2857_ = lean_ctor_get(v___y_2799_, 4);
v_synthPendingDepth_2858_ = lean_ctor_get(v___y_2799_, 5);
v_customCanUnfoldPredicate_x3f_2859_ = lean_ctor_get(v___y_2799_, 6);
v_univApprox_2860_ = lean_ctor_get_uint8(v___y_2799_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2861_ = lean_ctor_get_uint8(v___y_2799_, sizeof(void*)*7 + 2);
v_cacheInferType_2862_ = lean_ctor_get_uint8(v___y_2799_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2852_);
v___x_2863_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2849_, v_keyedConfig_2852_);
lean_inc(v_customCanUnfoldPredicate_x3f_2859_);
lean_inc(v_synthPendingDepth_2858_);
lean_inc(v_defEqCtx_x3f_2857_);
lean_inc_ref(v_localInstances_2856_);
lean_inc_ref(v_lctx_2855_);
lean_inc(v_zetaDeltaSet_2854_);
v___x_2864_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v_zetaDeltaSet_2854_);
lean_ctor_set(v___x_2864_, 2, v_lctx_2855_);
lean_ctor_set(v___x_2864_, 3, v_localInstances_2856_);
lean_ctor_set(v___x_2864_, 4, v_defEqCtx_x3f_2857_);
lean_ctor_set(v___x_2864_, 5, v_synthPendingDepth_2858_);
lean_ctor_set(v___x_2864_, 6, v_customCanUnfoldPredicate_x3f_2859_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*7, v_trackZetaDelta_2853_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*7 + 1, v_univApprox_2860_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2861_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*7 + 3, v_cacheInferType_2862_);
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
v___x_2865_ = lean_whnf(v___x_2850_, v___x_2864_, v___y_2800_, v___y_2801_, v___y_2802_);
v___y_2834_ = v___x_2865_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2866_; 
lean_inc(v___y_2802_);
lean_inc_ref(v___y_2801_);
lean_inc(v___y_2800_);
lean_inc_ref(v___y_2799_);
v___x_2866_ = lean_whnf(v___x_2850_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
v___y_2834_ = v___x_2866_;
goto v___jp_2833_;
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_box(0);
lean_inc(v_a_2797_);
v___x_2868_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2832_, v_a_2797_, v___x_2867_, v_fst_2830_, v_fst_2831_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
lean_dec(v_fst_2831_);
v___y_2805_ = v___x_2868_;
goto v___jp_2804_;
}
v___jp_2833_:
{
if (lean_obj_tag(v___y_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_a_2835_ = lean_ctor_get(v___y_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___y_2834_, 1);
v___x_2836_ = lean_box(0);
lean_inc(v_a_2797_);
v___x_2837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2832_, v_a_2797_, v___x_2836_, v_a_2835_, v_a_2797_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
v___y_2805_ = v___x_2837_;
goto v___jp_2804_;
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_snd_2832_);
lean_dec(v_a_2797_);
v_a_2838_ = lean_ctor_get(v___y_2834_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___y_2834_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___y_2834_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___y_2834_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
v___jp_2804_:
{
if (lean_obj_tag(v___y_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2818_; 
v_a_2806_ = lean_ctor_get(v___y_2805_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___y_2805_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2808_ = v___y_2805_;
v_isShared_2809_ = v_isSharedCheck_2818_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___y_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2818_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
if (lean_obj_tag(v_a_2806_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; 
lean_dec(v_a_2797_);
v_a_2810_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v_a_2806_, 1);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v_a_2810_);
v___x_2812_ = v___x_2808_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_del_object(v___x_2808_);
v_a_2814_ = lean_ctor_get(v_a_2806_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v_a_2806_, 1);
v___x_2815_ = lean_unsigned_to_nat(1u);
v___x_2816_ = lean_nat_add(v_a_2797_, v___x_2815_);
lean_dec(v_a_2797_);
v_a_2797_ = v___x_2816_;
v_b_2798_ = v_a_2814_;
goto _start;
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec(v_a_2797_);
v_a_2819_ = lean_ctor_get(v___y_2805_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___y_2805_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___y_2805_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___y_2805_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object* v_upperBound_2869_, lean_object* v_xs_2870_, lean_object* v_a_2871_, lean_object* v_b_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_2869_, v_xs_2870_, v_a_2871_, v_b_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v_xs_2870_);
lean_dec(v_upperBound_2869_);
return v_res_2878_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2));
v___x_2886_ = l_Lean_stringToMessageData(v___x_2885_);
return v___x_2886_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4));
v___x_2889_ = l_Lean_stringToMessageData(v___x_2888_);
return v___x_2889_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_unsigned_to_nat(0u);
v___x_2891_ = lean_nat_to_int(v___x_2890_);
return v___x_2891_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_nat_to_int(v___x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8));
v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object* v_tacticName_2897_, uint8_t v_explicit_2898_, lean_object* v_f_2899_, lean_object* v_xs_2900_, lean_object* v_i_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___y_2908_; lean_object* v_lower_2909_; lean_object* v_upper_2910_; lean_object* v___y_2916_; lean_object* v_lower_2917_; lean_object* v_upper_2918_; 
if (v_explicit_2898_ == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_2905_);
lean_inc_ref(v_a_2904_);
lean_inc(v_a_2903_);
lean_inc_ref(v_a_2902_);
lean_inc_ref(v_f_2899_);
v___x_2924_ = lean_infer_type(v_f_2899_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = lean_array_get_size(v_xs_2900_);
v___x_2927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1));
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v_a_2925_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v___x_2926_, v_xs_2900_, v___x_2923_, v___x_2928_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v_snd_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2989_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref_known(v___x_2929_, 1);
v_snd_2931_ = lean_ctor_get(v_a_2930_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_a_2930_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_a_2930_, 0);
lean_dec(v_unused_2990_);
v___x_2933_ = v_a_2930_;
v_isShared_2934_ = v_isSharedCheck_2989_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_snd_2931_);
lean_dec(v_a_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2989_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_snd_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2987_; 
v_snd_2935_ = lean_ctor_get(v_snd_2931_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_snd_2931_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_snd_2931_, 0);
lean_dec(v_unused_2988_);
v___x_2937_ = v_snd_2931_;
v_isShared_2938_ = v_isSharedCheck_2987_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_snd_2935_);
lean_dec(v_snd_2931_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2987_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___y_2940_; lean_object* v___y_2948_; lean_object* v___x_2974_; lean_object* v___y_2976_; uint8_t v___x_2981_; 
v___x_2974_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_2981_ = lean_int_dec_lt(v___x_2974_, v_i_2901_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2982_ = lean_array_get_size(v_snd_2935_);
v___x_2983_ = lean_nat_to_int(v___x_2982_);
v___x_2984_ = lean_int_add(v_i_2901_, v___x_2983_);
lean_dec(v___x_2983_);
v___y_2976_ = v___x_2984_;
goto v___jp_2975_;
}
else
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_2986_ = lean_int_sub(v_i_2901_, v___x_2985_);
v___y_2976_ = v___x_2986_;
goto v___jp_2975_;
}
v___jp_2939_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2941_ = lean_nat_abs(v___y_2940_);
lean_dec(v___y_2940_);
v___x_2942_ = lean_array_get(v___x_2923_, v_snd_2935_, v___x_2941_);
lean_dec(v___x_2941_);
lean_dec(v_snd_2935_);
lean_inc(v___x_2942_);
lean_inc_ref(v_xs_2900_);
v___x_2943_ = l_Array_toSubarray___redArg(v_xs_2900_, v___x_2923_, v___x_2942_);
v___x_2944_ = l_Subarray_copy___redArg(v___x_2943_);
v___x_2945_ = l_Lean_mkAppN(v_f_2899_, v___x_2944_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = lean_nat_dec_le(v___x_2942_, v___x_2923_);
if (v___x_2946_ == 0)
{
v___y_2916_ = v___x_2945_;
v_lower_2917_ = v___x_2942_;
v_upper_2918_ = v___x_2926_;
goto v___jp_2915_;
}
else
{
lean_dec(v___x_2942_);
v___y_2916_ = v___x_2945_;
v_lower_2917_ = v___x_2923_;
v_upper_2918_ = v___x_2926_;
goto v___jp_2915_;
}
}
v___jp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
lean_dec(v___y_2948_);
v___x_2949_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_2950_ = l_Lean_stringToMessageData(v_tacticName_2897_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set_tag(v___x_2937_, 7);
lean_ctor_set(v___x_2937_, 1, v___x_2950_);
lean_ctor_set(v___x_2937_, 0, v___x_2949_);
v___x_2952_ = v___x_2937_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___x_2950_);
v___x_2952_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
v___x_2953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 7);
lean_ctor_set(v___x_2933_, 1, v___x_2953_);
lean_ctor_set(v___x_2933_, 0, v___x_2952_);
v___x_2955_ = v___x_2933_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v___x_2956_ = lean_array_get_size(v_snd_2935_);
lean_dec(v_snd_2935_);
v___x_2957_ = l_Nat_reprFast(v___x_2956_);
v___x_2958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
v___x_2959_ = l_Lean_MessageData_ofFormat(v___x_2958_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2955_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5);
v___x_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2960_);
lean_ctor_set(v___x_2962_, 1, v___x_2961_);
v___x_2963_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2962_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
v___jp_2975_:
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_int_dec_lt(v___y_2976_, v___x_2974_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v___x_2978_ = lean_array_get_size(v_snd_2935_);
v___x_2979_ = lean_nat_to_int(v___x_2978_);
v___x_2980_ = lean_int_dec_le(v___x_2979_, v___y_2976_);
lean_dec(v___x_2979_);
if (v___x_2980_ == 0)
{
lean_del_object(v___x_2937_);
lean_del_object(v___x_2933_);
lean_dec_ref(v_tacticName_2897_);
v___y_2940_ = v___y_2976_;
goto v___jp_2939_;
}
else
{
lean_dec_ref(v_xs_2900_);
lean_dec_ref(v_f_2899_);
v___y_2948_ = v___y_2976_;
goto v___jp_2947_;
}
}
else
{
lean_dec_ref(v_xs_2900_);
lean_dec_ref(v_f_2899_);
v___y_2948_ = v___y_2976_;
goto v___jp_2947_;
}
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v_xs_2900_);
lean_dec_ref(v_f_2899_);
lean_dec_ref(v_tacticName_2897_);
v_a_2991_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2929_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2929_);
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
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_xs_2900_);
lean_dec_ref(v_f_2899_);
lean_dec_ref(v_tacticName_2897_);
v_a_2999_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2924_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2924_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
lean_object* v___x_3007_; lean_object* v___y_3009_; lean_object* v___y_3017_; lean_object* v___x_3039_; lean_object* v___y_3041_; uint8_t v___x_3046_; 
v___x_3007_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3046_ = lean_int_dec_lt(v___x_3039_, v_i_2901_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = lean_array_get_size(v_xs_2900_);
v___x_3048_ = lean_nat_to_int(v___x_3047_);
v___x_3049_ = lean_int_add(v_i_2901_, v___x_3048_);
lean_dec(v___x_3048_);
v___y_3041_ = v___x_3049_;
goto v___jp_3040_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3051_ = lean_int_sub(v_i_2901_, v___x_3050_);
v___y_3041_ = v___x_3051_;
goto v___jp_3040_;
}
v___jp_3008_:
{
lean_object* v_idx_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_idx_3010_ = lean_nat_abs(v___y_3009_);
lean_dec(v___y_3009_);
lean_inc(v_idx_3010_);
lean_inc_ref(v_xs_2900_);
v___x_3011_ = l_Array_toSubarray___redArg(v_xs_2900_, v___x_3007_, v_idx_3010_);
v___x_3012_ = l_Subarray_copy___redArg(v___x_3011_);
v___x_3013_ = l_Lean_mkAppN(v_f_2899_, v___x_3012_);
lean_dec_ref(v___x_3012_);
v___x_3014_ = lean_array_get_size(v_xs_2900_);
v___x_3015_ = lean_nat_dec_le(v_idx_3010_, v___x_3007_);
if (v___x_3015_ == 0)
{
v___y_2908_ = v___x_3013_;
v_lower_2909_ = v_idx_3010_;
v_upper_2910_ = v___x_3014_;
goto v___jp_2907_;
}
else
{
lean_dec(v_idx_3010_);
v___y_2908_ = v___x_3013_;
v_lower_2909_ = v___x_3007_;
v_upper_2910_ = v___x_3014_;
goto v___jp_2907_;
}
}
v___jp_3016_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec(v___y_3017_);
v___x_3018_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3019_ = l_Lean_stringToMessageData(v_tacticName_2897_);
v___x_3020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3018_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
v___x_3022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3020_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_array_get_size(v_xs_2900_);
lean_dec_ref(v_xs_2900_);
v___x_3024_ = l_Nat_reprFast(v___x_3023_);
v___x_3025_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
v___x_3026_ = l_Lean_MessageData_ofFormat(v___x_3025_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3022_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3029_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
v___jp_3040_:
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_int_dec_lt(v___y_3041_, v___x_3039_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___x_3045_; 
v___x_3043_ = lean_array_get_size(v_xs_2900_);
v___x_3044_ = lean_nat_to_int(v___x_3043_);
v___x_3045_ = lean_int_dec_le(v___x_3044_, v___y_3041_);
lean_dec(v___x_3044_);
if (v___x_3045_ == 0)
{
lean_dec_ref(v_tacticName_2897_);
v___y_3009_ = v___y_3041_;
goto v___jp_3008_;
}
else
{
lean_dec_ref(v_f_2899_);
v___y_3017_ = v___y_3041_;
goto v___jp_3016_;
}
}
else
{
lean_dec_ref(v_f_2899_);
v___y_3017_ = v___y_3041_;
goto v___jp_3016_;
}
}
}
v___jp_2907_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2911_ = l_Array_toSubarray___redArg(v_xs_2900_, v_lower_2909_, v_upper_2910_);
v___x_2912_ = l_Subarray_copy___redArg(v___x_2911_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___y_2908_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
return v___x_2914_;
}
v___jp_2915_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2919_ = l_Array_toSubarray___redArg(v_xs_2900_, v_lower_2917_, v_upper_2918_);
v___x_2920_ = l_Subarray_copy___redArg(v___x_2919_);
v___x_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___y_2916_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object* v_tacticName_3052_, lean_object* v_explicit_3053_, lean_object* v_f_3054_, lean_object* v_xs_3055_, lean_object* v_i_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
uint8_t v_explicit_boxed_3062_; lean_object* v_res_3063_; 
v_explicit_boxed_3062_ = lean_unbox(v_explicit_3053_);
v_res_3063_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3052_, v_explicit_boxed_3062_, v_f_3054_, v_xs_3055_, v_i_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_i_3056_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object* v_upperBound_3064_, lean_object* v_xs_3065_, lean_object* v_inst_3066_, lean_object* v_R_3067_, lean_object* v_a_3068_, lean_object* v_b_3069_, lean_object* v_c_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_3064_, v_xs_3065_, v_a_3068_, v_b_3069_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object* v_upperBound_3077_, lean_object* v_xs_3078_, lean_object* v_inst_3079_, lean_object* v_R_3080_, lean_object* v_a_3081_, lean_object* v_b_3082_, lean_object* v_c_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(v_upperBound_3077_, v_xs_3078_, v_inst_3079_, v_R_3080_, v_a_3081_, v_b_3082_, v_c_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec_ref(v_xs_3078_);
lean_dec(v_upperBound_3077_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object* v_tacticName_3090_, uint8_t v_explicit_3091_, lean_object* v_i_3092_, lean_object* v_mvarId_3093_, lean_object* v_snd_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
if (lean_obj_tag(v_x_3095_) == 5)
{
lean_object* v_fn_3103_; lean_object* v_arg_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v_fn_3103_ = lean_ctor_get(v_x_3095_, 0);
lean_inc_ref(v_fn_3103_);
v_arg_3104_ = lean_ctor_get(v_x_3095_, 1);
lean_inc_ref(v_arg_3104_);
lean_dec_ref_known(v_x_3095_, 2);
v___x_3105_ = lean_array_set(v_x_3096_, v_x_3097_, v_arg_3104_);
v___x_3106_ = lean_unsigned_to_nat(1u);
v___x_3107_ = lean_nat_sub(v_x_3097_, v___x_3106_);
lean_dec(v_x_3097_);
v_x_3095_ = v_fn_3103_;
v_x_3096_ = v___x_3105_;
v_x_3097_ = v___x_3107_;
goto _start;
}
else
{
lean_object* v___x_3109_; 
lean_dec(v_x_3097_);
lean_inc_ref(v_tacticName_3090_);
v___x_3109_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3090_, v_explicit_3091_, v_x_3095_, v_x_3096_, v_i_3092_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_fst_3111_; lean_object* v_snd_3112_; lean_object* v___x_3113_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v_fst_3111_ = lean_ctor_get(v_a_3110_, 0);
lean_inc(v_fst_3111_);
v_snd_3112_ = lean_ctor_get(v_a_3110_, 1);
lean_inc(v_snd_3112_);
lean_dec(v_a_3110_);
lean_inc(v_mvarId_3093_);
v___x_3113_ = l_Lean_MVarId_getTag(v_mvarId_3093_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3115_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
lean_inc_ref(v_tacticName_3090_);
v___x_3115_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_3090_, v_a_3114_, v_fst_3111_, v_snd_3112_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v_snd_3117_; lean_object* v_fst_3118_; lean_object* v_fst_3119_; lean_object* v_snd_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3146_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3115_, 1);
v_snd_3117_ = lean_ctor_get(v_a_3116_, 1);
lean_inc(v_snd_3117_);
v_fst_3118_ = lean_ctor_get(v_a_3116_, 0);
lean_inc(v_fst_3118_);
lean_dec(v_a_3116_);
v_fst_3119_ = lean_ctor_get(v_snd_3117_, 0);
v_snd_3120_ = lean_ctor_get(v_snd_3117_, 1);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_snd_3117_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3122_ = v_snd_3117_;
v_isShared_3123_ = v_isSharedCheck_3146_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_snd_3120_);
lean_inc(v_fst_3119_);
lean_dec(v_snd_3117_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3146_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; 
lean_inc(v_fst_3118_);
v___x_3124_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_3090_, v_snd_3094_, v_fst_3118_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref_known(v___x_3124_, 1);
v___x_3125_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_3093_, v_fst_3118_, v___y_3099_);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3125_, 0);
lean_dec(v_unused_3137_);
v___x_3127_ = v___x_3125_;
v_isShared_3128_ = v_isSharedCheck_3136_;
goto v_resetjp_3126_;
}
else
{
lean_dec(v___x_3125_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3136_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3129_ = lean_array_to_list(v_snd_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 1);
lean_ctor_set(v___x_3122_, 1, v___x_3129_);
v___x_3131_ = v___x_3122_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_fst_3119_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3133_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3131_);
v___x_3133_ = v___x_3127_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_del_object(v___x_3122_);
lean_dec(v_snd_3120_);
lean_dec(v_fst_3119_);
lean_dec(v_fst_3118_);
lean_dec(v_mvarId_3093_);
v_a_3138_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3124_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3124_);
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
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v_snd_3094_);
lean_dec(v_mvarId_3093_);
lean_dec_ref(v_tacticName_3090_);
v_a_3147_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3115_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3115_);
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
lean_dec(v_snd_3112_);
lean_dec(v_fst_3111_);
lean_dec_ref(v_snd_3094_);
lean_dec(v_mvarId_3093_);
lean_dec_ref(v_tacticName_3090_);
v_a_3155_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3113_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3113_);
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
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v_snd_3094_);
lean_dec(v_mvarId_3093_);
lean_dec_ref(v_tacticName_3090_);
v_a_3163_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3109_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3109_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object* v_tacticName_3171_, lean_object* v_explicit_3172_, lean_object* v_i_3173_, lean_object* v_mvarId_3174_, lean_object* v_snd_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_, lean_object* v_x_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
uint8_t v_explicit_boxed_3184_; lean_object* v_res_3185_; 
v_explicit_boxed_3184_ = lean_unbox(v_explicit_3172_);
v_res_3185_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3171_, v_explicit_boxed_3184_, v_i_3173_, v_mvarId_3174_, v_snd_3175_, v_x_3176_, v_x_3177_, v_x_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_i_3173_);
return v_res_3185_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_unsigned_to_nat(2u);
v___x_3187_ = lean_nat_to_int(v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3189_ = lean_int_neg(v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2));
v___x_3192_ = l_Lean_stringToMessageData(v___x_3191_);
return v___x_3192_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4));
v___x_3195_ = l_Lean_stringToMessageData(v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object* v_mvarId_3196_, lean_object* v_tacticName_3197_, uint8_t v_explicit_3198_, lean_object* v_i_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
lean_inc(v_mvarId_3196_);
v___x_3205_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_3196_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v_fst_3207_; lean_object* v_snd_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3267_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3205_, 1);
v_fst_3207_ = lean_ctor_get(v_a_3206_, 0);
v_snd_3208_ = lean_ctor_get(v_a_3206_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_a_3206_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3210_ = v_a_3206_;
v_isShared_3211_ = v_isSharedCheck_3267_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_snd_3208_);
lean_inc(v_fst_3207_);
lean_dec(v_a_3206_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3267_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v_a_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; uint8_t v___y_3245_; 
v___x_3212_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_3207_, v___y_3201_);
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref(v___x_3212_);
v___x_3214_ = l_Lean_Expr_cleanupAnnotations(v_a_3213_);
v___x_3215_ = l_Lean_Expr_isForall(v___x_3214_);
if (v___x_3215_ == 0)
{
uint8_t v___x_3248_; 
lean_del_object(v___x_3210_);
v___x_3248_ = l_Lean_Expr_isApp(v___x_3214_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_dec(v_snd_3208_);
lean_dec(v_mvarId_3196_);
v___x_3249_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3250_ = l_Lean_stringToMessageData(v_tacticName_3197_);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5);
v___x_3253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3251_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = l_Lean_indentExpr(v___x_3214_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3255_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3256_;
}
else
{
lean_object* v_dummy_3257_; lean_object* v_nargs_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v_dummy_3257_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_3258_ = l_Lean_Expr_getAppNumArgs(v___x_3214_);
lean_inc(v_nargs_3258_);
v___x_3259_ = lean_mk_array(v_nargs_3258_, v_dummy_3257_);
v___x_3260_ = lean_unsigned_to_nat(1u);
v___x_3261_ = lean_nat_sub(v_nargs_3258_, v___x_3260_);
lean_dec(v_nargs_3258_);
v___x_3262_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3197_, v_explicit_3198_, v_i_3199_, v_mvarId_3196_, v_snd_3208_, v___x_3214_, v___x_3259_, v___x_3261_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3262_;
}
}
else
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3264_ = lean_int_dec_lt(v_i_3199_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3266_ = lean_int_dec_eq(v_i_3199_, v___x_3265_);
v___y_3245_ = v___x_3266_;
goto v___jp_3244_;
}
else
{
v___y_3245_ = v___x_3215_;
goto v___jp_3244_;
}
}
v___jp_3216_:
{
lean_object* v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3222_ = lean_int_dec_eq(v_i_3199_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; uint8_t v___x_3224_; lean_object* v___x_3225_; 
v___x_3223_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3224_ = lean_int_dec_eq(v_i_3199_, v___x_3223_);
v___x_3225_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3197_, v___x_3224_, v_mvarId_3196_, v___x_3214_, v_snd_3208_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3225_;
}
else
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3197_, v___x_3215_, v_mvarId_3196_, v___x_3214_, v_snd_3208_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
return v___x_3226_;
}
}
v___jp_3227_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3228_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3229_ = l_Lean_stringToMessageData(v_tacticName_3197_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set_tag(v___x_3210_, 7);
lean_ctor_set(v___x_3210_, 1, v___x_3229_);
lean_ctor_set(v___x_3210_, 0, v___x_3228_);
v___x_3231_ = v___x_3210_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
v___x_3232_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3);
v___x_3233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3231_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3233_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
v___jp_3244_:
{
if (v___y_3245_ == 0)
{
lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3246_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3247_ = lean_int_dec_lt(v___x_3246_, v_i_3199_);
if (v___x_3247_ == 0)
{
lean_del_object(v___x_3210_);
v___y_3217_ = v___y_3200_;
v___y_3218_ = v___y_3201_;
v___y_3219_ = v___y_3202_;
v___y_3220_ = v___y_3203_;
goto v___jp_3216_;
}
else
{
lean_dec_ref(v___x_3214_);
lean_dec(v_snd_3208_);
lean_dec(v_mvarId_3196_);
goto v___jp_3227_;
}
}
else
{
lean_dec_ref(v___x_3214_);
lean_dec(v_snd_3208_);
lean_dec(v_mvarId_3196_);
goto v___jp_3227_;
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v_tacticName_3197_);
lean_dec(v_mvarId_3196_);
v_a_3268_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3205_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3205_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object* v_mvarId_3276_, lean_object* v_tacticName_3277_, lean_object* v_explicit_3278_, lean_object* v_i_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
uint8_t v_explicit_boxed_3285_; lean_object* v_res_3286_; 
v_explicit_boxed_3285_ = lean_unbox(v_explicit_3278_);
v_res_3286_ = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(v_mvarId_3276_, v_tacticName_3277_, v_explicit_boxed_3285_, v_i_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v_i_3279_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object* v_tacticName_3287_, lean_object* v_mvarId_3288_, lean_object* v_i_3289_, uint8_t v_explicit_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_){
_start:
{
lean_object* v___x_3296_; lean_object* v___f_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_box(v_explicit_3290_);
lean_inc(v_mvarId_3288_);
v___f_3297_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3297_, 0, v_mvarId_3288_);
lean_closure_set(v___f_3297_, 1, v_tacticName_3287_);
lean_closure_set(v___f_3297_, 2, v___x_3296_);
lean_closure_set(v___f_3297_, 3, v_i_3289_);
v___x_3298_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_3288_, v___f_3297_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object* v_tacticName_3299_, lean_object* v_mvarId_3300_, lean_object* v_i_3301_, lean_object* v_explicit_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
uint8_t v_explicit_boxed_3308_; lean_object* v_res_3309_; 
v_explicit_boxed_3308_ = lean_unbox(v_explicit_3302_);
v_res_3309_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3299_, v_mvarId_3300_, v_i_3301_, v_explicit_boxed_3308_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object* v_tacticName_3310_, lean_object* v_i_3311_, uint8_t v_explicit_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3319_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3320_ = lean_int_dec_eq(v_i_3311_, v___x_3319_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v_a_3322_; lean_object* v___x_3323_; 
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v___x_3321_, 1);
v___x_3323_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3310_, v_a_3322_, v_i_3311_, v_explicit_3312_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3323_, 1);
v___x_3325_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3324_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
return v___x_3325_;
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
v_a_3326_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3323_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3323_);
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
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v_i_3311_);
lean_dec_ref(v_tacticName_3310_);
v_a_3334_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3321_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3321_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v___x_3342_; 
lean_dec(v_i_3311_);
lean_dec_ref(v_tacticName_3310_);
v___x_3342_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_a_3343_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3347_, 0, v_a_3345_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3347_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
return v___x_3348_;
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
v_a_3349_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3344_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3344_);
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
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
v_a_3357_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3342_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3342_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object* v_tacticName_3365_, lean_object* v_i_3366_, lean_object* v_explicit_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
uint8_t v_explicit_boxed_3374_; lean_object* v_res_3375_; 
v_explicit_boxed_3374_ = lean_unbox(v_explicit_3367_);
v_res_3375_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3365_, v_i_3366_, v_explicit_boxed_3374_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_a_3368_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object* v_tacticName_3376_, lean_object* v_i_3377_, uint8_t v_explicit_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3376_, v_i_3377_, v_explicit_3378_, v_a_3380_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object* v_tacticName_3389_, lean_object* v_i_3390_, lean_object* v_explicit_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
uint8_t v_explicit_boxed_3401_; lean_object* v_res_3402_; 
v_explicit_boxed_3401_ = lean_unbox(v_explicit_3391_);
v_res_3402_ = l_Lean_Elab_Tactic_Conv_evalArg(v_tacticName_3389_, v_i_3390_, v_explicit_boxed_3401_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
return v_res_3402_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_box(0);
v___x_3404_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___x_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg(){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object* v___y_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object* v_00_u03b1_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v___x_3421_; 
v___x_3421_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object* v_00_u03b1_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(v_00_u03b1_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object* v_stx_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_3461_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
lean_inc(v_stx_3450_);
v___x_3462_ = l_Lean_Syntax_isOfKind(v_stx_3450_, v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; 
lean_dec(v_stx_3450_);
v___x_3463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3463_;
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3490_; lean_object* v_neg_x3f_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; 
v___x_3464_ = lean_unsigned_to_nat(1u);
v___x_3465_ = l_Lean_Syntax_getArg(v_stx_3450_, v___x_3464_);
lean_dec(v_stx_3450_);
v___x_3466_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__3));
lean_inc(v___x_3465_);
v___x_3467_ = l_Lean_Syntax_isOfKind(v___x_3465_, v___x_3466_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v___x_3465_);
v___x_3508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3508_;
}
else
{
lean_object* v___x_3509_; lean_object* v_tk_x3f_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3509_ = lean_unsigned_to_nat(0u);
v___x_3527_ = l_Lean_Syntax_getArg(v___x_3465_, v___x_3509_);
v___x_3528_ = l_Lean_Syntax_isNone(v___x_3527_);
if (v___x_3528_ == 0)
{
uint8_t v___x_3529_; 
lean_inc(v___x_3527_);
v___x_3529_ = l_Lean_Syntax_matchesNull(v___x_3527_, v___x_3464_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
lean_dec(v___x_3527_);
lean_dec(v___x_3465_);
v___x_3530_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3530_;
}
else
{
lean_object* v_tk_x3f_3531_; lean_object* v___x_3532_; 
v_tk_x3f_3531_ = l_Lean_Syntax_getArg(v___x_3527_, v___x_3509_);
lean_dec(v___x_3527_);
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_tk_x3f_3531_);
v_tk_x3f_3511_ = v___x_3532_;
v___y_3512_ = v_a_3451_;
v___y_3513_ = v_a_3452_;
v___y_3514_ = v_a_3453_;
v___y_3515_ = v_a_3454_;
v___y_3516_ = v_a_3455_;
v___y_3517_ = v_a_3456_;
v___y_3518_ = v_a_3457_;
v___y_3519_ = v_a_3458_;
goto v___jp_3510_;
}
}
else
{
lean_object* v___x_3533_; 
lean_dec(v___x_3527_);
v___x_3533_ = lean_box(0);
v_tk_x3f_3511_ = v___x_3533_;
v___y_3512_ = v_a_3451_;
v___y_3513_ = v_a_3452_;
v___y_3514_ = v_a_3453_;
v___y_3515_ = v_a_3454_;
v___y_3516_ = v_a_3455_;
v___y_3517_ = v_a_3456_;
v___y_3518_ = v_a_3457_;
v___y_3519_ = v_a_3458_;
goto v___jp_3510_;
}
v___jp_3510_:
{
lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3520_ = l_Lean_Syntax_getArg(v___x_3465_, v___x_3464_);
v___x_3521_ = l_Lean_Syntax_isNone(v___x_3520_);
if (v___x_3521_ == 0)
{
uint8_t v___x_3522_; 
lean_inc(v___x_3520_);
v___x_3522_ = l_Lean_Syntax_matchesNull(v___x_3520_, v___x_3464_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; 
lean_dec(v___x_3520_);
lean_dec(v_tk_x3f_3511_);
lean_dec(v___x_3465_);
v___x_3523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3523_;
}
else
{
lean_object* v_neg_x3f_3524_; lean_object* v___x_3525_; 
v_neg_x3f_3524_ = l_Lean_Syntax_getArg(v___x_3520_, v___x_3509_);
lean_dec(v___x_3520_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_neg_x3f_3524_);
v___y_3490_ = v_tk_x3f_3511_;
v_neg_x3f_3491_ = v___x_3525_;
v___y_3492_ = v___y_3512_;
v___y_3493_ = v___y_3513_;
v___y_3494_ = v___y_3514_;
v___y_3495_ = v___y_3515_;
v___y_3496_ = v___y_3516_;
v___y_3497_ = v___y_3517_;
v___y_3498_ = v___y_3518_;
v___y_3499_ = v___y_3519_;
goto v___jp_3489_;
}
}
else
{
lean_object* v___x_3526_; 
lean_dec(v___x_3520_);
v___x_3526_ = lean_box(0);
v___y_3490_ = v_tk_x3f_3511_;
v_neg_x3f_3491_ = v___x_3526_;
v___y_3492_ = v___y_3512_;
v___y_3493_ = v___y_3513_;
v___y_3494_ = v___y_3514_;
v___y_3495_ = v___y_3515_;
v___y_3496_ = v___y_3516_;
v___y_3497_ = v___y_3517_;
v___y_3498_ = v___y_3518_;
v___y_3499_ = v___y_3519_;
goto v___jp_3489_;
}
}
}
v___jp_3468_:
{
if (lean_obj_tag(v___y_3473_) == 0)
{
uint8_t v___x_3476_; lean_object* v___x_3477_; 
v___x_3476_ = 0;
v___x_3477_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3460_, v___y_3475_, v___x_3476_, v___y_3474_, v___y_3469_, v___y_3472_, v___y_3470_, v___y_3471_);
return v___x_3477_;
}
else
{
lean_object* v___x_3478_; 
lean_dec_ref_known(v___y_3473_, 1);
v___x_3478_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3460_, v___y_3475_, v___x_3467_, v___y_3474_, v___y_3469_, v___y_3472_, v___y_3470_, v___y_3471_);
return v___x_3478_;
}
}
v___jp_3479_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = l_Lean_TSyntax_getNat(v___y_3486_);
lean_dec(v___y_3486_);
v___x_3488_ = lean_nat_to_int(v___x_3487_);
v___y_3469_ = v___y_3480_;
v___y_3470_ = v___y_3481_;
v___y_3471_ = v___y_3483_;
v___y_3472_ = v___y_3482_;
v___y_3473_ = v___y_3484_;
v___y_3474_ = v___y_3485_;
v___y_3475_ = v___x_3488_;
goto v___jp_3468_;
}
v___jp_3489_:
{
lean_object* v___x_3500_; lean_object* v_i_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3500_ = lean_unsigned_to_nat(2u);
v_i_3501_ = l_Lean_Syntax_getArg(v___x_3465_, v___x_3500_);
lean_dec(v___x_3465_);
v___x_3502_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__5));
lean_inc(v_i_3501_);
v___x_3503_ = l_Lean_Syntax_isOfKind(v_i_3501_, v___x_3502_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; 
lean_dec(v_i_3501_);
lean_dec(v_neg_x3f_3491_);
lean_dec(v___y_3490_);
v___x_3504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3504_;
}
else
{
if (lean_obj_tag(v_neg_x3f_3491_) == 0)
{
v___y_3480_ = v___y_3496_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3497_;
v___y_3483_ = v___y_3499_;
v___y_3484_ = v___y_3490_;
v___y_3485_ = v___y_3493_;
v___y_3486_ = v_i_3501_;
goto v___jp_3479_;
}
else
{
lean_dec_ref_known(v_neg_x3f_3491_, 1);
if (v___x_3467_ == 0)
{
v___y_3480_ = v___y_3496_;
v___y_3481_ = v___y_3498_;
v___y_3482_ = v___y_3497_;
v___y_3483_ = v___y_3499_;
v___y_3484_ = v___y_3490_;
v___y_3485_ = v___y_3493_;
v___y_3486_ = v_i_3501_;
goto v___jp_3479_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3505_ = l_Lean_TSyntax_getNat(v_i_3501_);
lean_dec(v_i_3501_);
v___x_3506_ = lean_nat_to_int(v___x_3505_);
v___x_3507_ = lean_int_neg(v___x_3506_);
lean_dec(v___x_3506_);
v___y_3469_ = v___y_3496_;
v___y_3470_ = v___y_3498_;
v___y_3471_ = v___y_3499_;
v___y_3472_ = v___y_3497_;
v___y_3473_ = v___y_3490_;
v___y_3474_ = v___y_3493_;
v___y_3475_ = v___x_3507_;
goto v___jp_3468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object* v_stx_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Elab_Tactic_Conv_elabArg(v_stx_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1(){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3553_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3554_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
v___x_3555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1));
v___x_3556_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_elabArg___boxed), 10, 0);
v___x_3557_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3553_, v___x_3554_, v___x_3555_, v___x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object* v_a_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; uint8_t v___x_3569_; lean_object* v___x_3570_; 
v___x_3567_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0));
v___x_3568_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3569_ = 0;
v___x_3570_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3567_, v___x_3568_, v___x_3569_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object* v_x_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3580_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object* v_x_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Elab_Tactic_Conv_evalLhs(v_x_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_a_3592_);
lean_dec(v_a_3591_);
lean_dec_ref(v_a_3590_);
lean_dec(v_x_3589_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1(){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3614_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0));
v___x_3616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3617_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLhs___boxed), 10, 0);
v___x_3618_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3614_, v___x_3615_, v___x_3616_, v___x_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object* v_a_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3(){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3648_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6));
v___x_3649_ = l_Lean_addBuiltinDeclarationRanges(v___x_3647_, v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
return v_res_3651_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3654_ = lean_int_neg(v___x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; lean_object* v___x_3664_; 
v___x_3661_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0));
v___x_3662_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1, &l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1);
v___x_3663_ = 0;
v___x_3664_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3661_, v___x_3662_, v___x_3663_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
lean_dec(v_a_3667_);
lean_dec_ref(v_a_3666_);
lean_dec(v_a_3665_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object* v_x_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3674_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object* v_x_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Elab_Tactic_Conv_evalRhs(v_x_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec(v_a_3689_);
lean_dec_ref(v_a_3688_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_x_3683_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1(){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3708_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0));
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3711_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRhs___boxed), 10, 0);
v___x_3712_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3708_, v___x_3709_, v___x_3710_, v___x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object* v_a_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
return v_res_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3(){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3741_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6));
v___x_3743_ = l_Lean_addBuiltinDeclarationRanges(v___x_3741_, v___x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object* v_a_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object* v_e_3746_, lean_object* v___y_3747_){
_start:
{
uint8_t v___x_3749_; 
v___x_3749_ = l_Lean_Expr_hasMVar(v_e_3746_);
if (v___x_3749_ == 0)
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_e_3746_);
return v___x_3750_;
}
else
{
lean_object* v___x_3751_; lean_object* v_mctx_3752_; lean_object* v___x_3753_; lean_object* v_fst_3754_; lean_object* v_snd_3755_; lean_object* v___x_3756_; lean_object* v_cache_3757_; lean_object* v_zetaDeltaFVarIds_3758_; lean_object* v_postponed_3759_; lean_object* v_diag_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3769_; 
v___x_3751_ = lean_st_ref_get(v___y_3747_);
v_mctx_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc_ref(v_mctx_3752_);
lean_dec(v___x_3751_);
v___x_3753_ = l_Lean_instantiateMVarsCore(v_mctx_3752_, v_e_3746_);
v_fst_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_fst_3754_);
v_snd_3755_ = lean_ctor_get(v___x_3753_, 1);
lean_inc(v_snd_3755_);
lean_dec_ref(v___x_3753_);
v___x_3756_ = lean_st_ref_take(v___y_3747_);
v_cache_3757_ = lean_ctor_get(v___x_3756_, 1);
v_zetaDeltaFVarIds_3758_ = lean_ctor_get(v___x_3756_, 2);
v_postponed_3759_ = lean_ctor_get(v___x_3756_, 3);
v_diag_3760_ = lean_ctor_get(v___x_3756_, 4);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; 
v_unused_3770_ = lean_ctor_get(v___x_3756_, 0);
lean_dec(v_unused_3770_);
v___x_3762_ = v___x_3756_;
v_isShared_3763_ = v_isSharedCheck_3769_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_diag_3760_);
lean_inc(v_postponed_3759_);
lean_inc(v_zetaDeltaFVarIds_3758_);
lean_inc(v_cache_3757_);
lean_dec(v___x_3756_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3769_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v_snd_3755_);
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_snd_3755_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_cache_3757_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v_zetaDeltaFVarIds_3758_);
lean_ctor_set(v_reuseFailAlloc_3768_, 3, v_postponed_3759_);
lean_ctor_set(v_reuseFailAlloc_3768_, 4, v_diag_3760_);
v___x_3765_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = lean_st_ref_put(v___y_3747_, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v_fst_3754_);
return v___x_3767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object* v_e_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3771_, v___y_3772_);
lean_dec(v___y_3772_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object* v_e_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3775_, v___y_3781_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object* v_e_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(v_e_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object* v_x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; 
lean_inc(v___y_3801_);
lean_inc_ref(v___y_3800_);
lean_inc(v___y_3799_);
lean_inc_ref(v___y_3798_);
v___x_3807_ = lean_apply_9(v_x_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, lean_box(0));
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object* v_x_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(v_x_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object* v_mvarId_3819_, lean_object* v_x_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v___f_3830_; lean_object* v___x_3831_; 
lean_inc(v___y_3824_);
lean_inc_ref(v___y_3823_);
lean_inc(v___y_3822_);
lean_inc_ref(v___y_3821_);
v___f_3830_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3830_, 0, v_x_3820_);
lean_closure_set(v___f_3830_, 1, v___y_3821_);
lean_closure_set(v___f_3830_, 2, v___y_3822_);
lean_closure_set(v___f_3830_, 3, v___y_3823_);
lean_closure_set(v___f_3830_, 4, v___y_3824_);
v___x_3831_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3819_, v___f_3830_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3831_) == 0)
{
return v___x_3831_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object* v_mvarId_3840_, lean_object* v_x_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3840_, v_x_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object* v_00_u03b1_3852_, lean_object* v_mvarId_3853_, lean_object* v_x_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3853_, v_x_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object* v_00_u03b1_3865_, lean_object* v_mvarId_3866_, lean_object* v_x_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(v_00_u03b1_3865_, v_mvarId_3866_, v_x_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object* v_msg_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_ref_3884_; lean_object* v___x_3885_; lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3894_; 
v_ref_3884_ = lean_ctor_get(v___y_3881_, 2);
v___x_3885_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3894_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3894_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; lean_object* v___x_3892_; 
lean_inc(v_ref_3884_);
v___x_3890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3890_, 0, v_ref_3884_);
lean_ctor_set(v___x_3890_, 1, v_a_3886_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set_tag(v___x_3888_, 1);
lean_ctor_set(v___x_3888_, 0, v___x_3890_);
v___x_3892_ = v___x_3888_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object* v_msg_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object* v_mvarId_3902_, lean_object* v_val_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___x_3906_; lean_object* v_mctx_3907_; lean_object* v_cache_3908_; lean_object* v_zetaDeltaFVarIds_3909_; lean_object* v_postponed_3910_; lean_object* v_diag_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3941_; 
v___x_3906_ = lean_st_ref_take(v___y_3904_);
v_mctx_3907_ = lean_ctor_get(v___x_3906_, 0);
v_cache_3908_ = lean_ctor_get(v___x_3906_, 1);
v_zetaDeltaFVarIds_3909_ = lean_ctor_get(v___x_3906_, 2);
v_postponed_3910_ = lean_ctor_get(v___x_3906_, 3);
v_diag_3911_ = lean_ctor_get(v___x_3906_, 4);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3913_ = v___x_3906_;
v_isShared_3914_ = v_isSharedCheck_3941_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_diag_3911_);
lean_inc(v_postponed_3910_);
lean_inc(v_zetaDeltaFVarIds_3909_);
lean_inc(v_cache_3908_);
lean_inc(v_mctx_3907_);
lean_dec(v___x_3906_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3941_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_depth_3915_; lean_object* v_levelAssignDepth_3916_; lean_object* v_lmvarCounter_3917_; lean_object* v_mvarCounter_3918_; lean_object* v_lDecls_3919_; lean_object* v_decls_3920_; lean_object* v_userNames_3921_; lean_object* v_lAssignment_3922_; lean_object* v_eAssignment_3923_; lean_object* v_dAssignment_3924_; lean_object* v_instanceTypedMVars_3925_; lean_object* v_synthNormMemo_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3940_; 
v_depth_3915_ = lean_ctor_get(v_mctx_3907_, 0);
v_levelAssignDepth_3916_ = lean_ctor_get(v_mctx_3907_, 1);
v_lmvarCounter_3917_ = lean_ctor_get(v_mctx_3907_, 2);
v_mvarCounter_3918_ = lean_ctor_get(v_mctx_3907_, 3);
v_lDecls_3919_ = lean_ctor_get(v_mctx_3907_, 4);
v_decls_3920_ = lean_ctor_get(v_mctx_3907_, 5);
v_userNames_3921_ = lean_ctor_get(v_mctx_3907_, 6);
v_lAssignment_3922_ = lean_ctor_get(v_mctx_3907_, 7);
v_eAssignment_3923_ = lean_ctor_get(v_mctx_3907_, 8);
v_dAssignment_3924_ = lean_ctor_get(v_mctx_3907_, 9);
v_instanceTypedMVars_3925_ = lean_ctor_get(v_mctx_3907_, 10);
v_synthNormMemo_3926_ = lean_ctor_get(v_mctx_3907_, 11);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_mctx_3907_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3928_ = v_mctx_3907_;
v_isShared_3929_ = v_isSharedCheck_3940_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_synthNormMemo_3926_);
lean_inc(v_instanceTypedMVars_3925_);
lean_inc(v_dAssignment_3924_);
lean_inc(v_eAssignment_3923_);
lean_inc(v_lAssignment_3922_);
lean_inc(v_userNames_3921_);
lean_inc(v_decls_3920_);
lean_inc(v_lDecls_3919_);
lean_inc(v_mvarCounter_3918_);
lean_inc(v_lmvarCounter_3917_);
lean_inc(v_levelAssignDepth_3916_);
lean_inc(v_depth_3915_);
lean_dec(v_mctx_3907_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3940_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3933_; 
v___x_3930_ = lean_box(0);
v___x_3931_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_3923_, v_mvarId_3902_, v_val_3903_);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 8, v___x_3931_);
v___x_3933_ = v___x_3928_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_depth_3915_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_levelAssignDepth_3916_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_lmvarCounter_3917_);
lean_ctor_set(v_reuseFailAlloc_3939_, 3, v_mvarCounter_3918_);
lean_ctor_set(v_reuseFailAlloc_3939_, 4, v_lDecls_3919_);
lean_ctor_set(v_reuseFailAlloc_3939_, 5, v_decls_3920_);
lean_ctor_set(v_reuseFailAlloc_3939_, 6, v_userNames_3921_);
lean_ctor_set(v_reuseFailAlloc_3939_, 7, v_lAssignment_3922_);
lean_ctor_set(v_reuseFailAlloc_3939_, 8, v___x_3931_);
lean_ctor_set(v_reuseFailAlloc_3939_, 9, v_dAssignment_3924_);
lean_ctor_set(v_reuseFailAlloc_3939_, 10, v_instanceTypedMVars_3925_);
lean_ctor_set(v_reuseFailAlloc_3939_, 11, v_synthNormMemo_3926_);
v___x_3933_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
lean_object* v___x_3935_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3933_);
v___x_3935_ = v___x_3913_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_cache_3908_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_zetaDeltaFVarIds_3909_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v_postponed_3910_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v_diag_3911_);
v___x_3935_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_st_ref_put(v___y_3904_, v___x_3935_);
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3930_);
return v___x_3937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object* v_mvarId_3942_, lean_object* v_val_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_3942_, v_val_3943_, v___y_3944_);
lean_dec(v___y_3944_);
return v_res_3946_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1));
v___x_3950_ = l_Lean_stringToMessageData(v___x_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object* v_a_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v___x_3961_; 
lean_inc(v_a_3951_);
v___x_3961_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_3951_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v_fst_3963_; lean_object* v_snd_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4016_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v_fst_3963_ = lean_ctor_get(v_a_3962_, 0);
v_snd_3964_ = lean_ctor_get(v_a_3962_, 1);
v_isSharedCheck_4016_ = !lean_is_exclusive(v_a_3962_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_3966_ = v_a_3962_;
v_isShared_3967_ = v_isSharedCheck_4016_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_snd_3964_);
lean_inc(v_fst_3963_);
lean_dec(v_a_3962_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4016_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v_a_3969_; lean_object* v___x_3970_; 
v___x_3968_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_fst_3963_, v___y_3957_);
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v___x_3970_ = l_Lean_Expr_cleanupAnnotations(v_a_3969_);
if (lean_obj_tag(v___x_3970_) == 5)
{
lean_object* v_fn_3971_; lean_object* v_arg_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_del_object(v___x_3966_);
v_fn_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc_ref(v_fn_3971_);
v_arg_3972_ = lean_ctor_get(v___x_3970_, 1);
lean_inc_ref(v_arg_3972_);
lean_dec_ref_known(v___x_3970_, 2);
v___x_3973_ = lean_box(0);
v___x_3974_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fn_3971_, v___x_3973_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v_fst_3976_; lean_object* v_snd_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_4001_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v_fst_3976_ = lean_ctor_get(v_a_3975_, 0);
v_snd_3977_ = lean_ctor_get(v_a_3975_, 1);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_a_3975_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3979_ = v_a_3975_;
v_isShared_3980_ = v_isSharedCheck_4001_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_snd_3977_);
lean_inc(v_fst_3976_);
lean_dec(v_a_3975_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_4001_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3981_; 
lean_inc_ref(v_arg_3972_);
lean_inc(v_snd_3977_);
v___x_3981_ = l_Lean_Meta_mkCongrFun(v_snd_3977_, v_arg_3972_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_a_3951_, v_a_3982_, v___y_3957_);
lean_dec_ref(v___x_3983_);
v___x_3984_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0));
v___x_3985_ = l_Lean_Expr_app___override(v_fst_3976_, v_arg_3972_);
v___x_3986_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_3984_, v_snd_3964_, v___x_3985_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
lean_dec_ref_known(v___x_3986_, 1);
v___x_3987_ = l_Lean_Expr_mvarId_x21(v_snd_3977_);
lean_dec(v_snd_3977_);
v___x_3988_ = lean_box(0);
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 1);
lean_ctor_set(v___x_3979_, 1, v___x_3988_);
lean_ctor_set(v___x_3979_, 0, v___x_3987_);
v___x_3990_ = v___x_3979_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3987_);
lean_ctor_set(v_reuseFailAlloc_3992_, 1, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3990_, v___y_3953_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
return v___x_3991_;
}
}
else
{
lean_del_object(v___x_3979_);
lean_dec(v_snd_3977_);
return v___x_3986_;
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_del_object(v___x_3979_);
lean_dec(v_snd_3977_);
lean_dec(v_fst_3976_);
lean_dec_ref(v_arg_3972_);
lean_dec(v_snd_3964_);
lean_dec(v_a_3951_);
v_a_3993_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3981_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3981_);
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
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_arg_3972_);
lean_dec(v_snd_3964_);
lean_dec(v_a_3951_);
v_a_4002_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3974_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3974_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4013_; 
lean_dec(v_snd_3964_);
lean_dec(v_a_3951_);
v___x_4010_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2);
v___x_4011_ = l_Lean_indentExpr(v___x_3970_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set_tag(v___x_3966_, 7);
lean_ctor_set(v___x_3966_, 1, v___x_4011_);
lean_ctor_set(v___x_3966_, 0, v___x_4010_);
v___x_4013_ = v___x_3966_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4010_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v___x_4013_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
return v___x_4014_;
}
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec(v_a_3951_);
v_a_4017_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_3961_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_3961_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object* v_a_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(v_a_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4037_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v___f_4047_; lean_object* v___x_4048_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc_n(v_a_4046_, 2);
lean_dec_ref_known(v___x_4045_, 1);
v___f_4047_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4047_, 0, v_a_4046_);
v___x_4048_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_a_4046_, v___f_4047_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
return v___x_4048_;
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
v_a_4049_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4045_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4045_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
lean_dec_ref(v_a_4061_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object* v_x_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object* v_x_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Lean_Elab_Tactic_Conv_evalFun(v_x_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
lean_dec(v_a_4084_);
lean_dec_ref(v_a_4083_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
lean_dec_ref(v_a_4079_);
lean_dec(v_x_4078_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object* v_mvarId_4089_, lean_object* v_val_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; 
v___x_4100_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_4089_, v_val_4090_, v___y_4096_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object* v_mvarId_4101_, lean_object* v_val_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(v_mvarId_4101_, v_val_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object* v_00_u03b1_4113_, lean_object* v_msg_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_4114_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object* v_00_u03b1_4125_, lean_object* v_msg_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(v_00_u03b1_4125_, v_msg_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1(){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4151_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4152_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0));
v___x_4153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4154_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___boxed), 10, 0);
v___x_4155_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4151_, v___x_4152_, v___x_4153_, v___x_4154_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3(){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4185_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6));
v___x_4186_ = l_Lean_addBuiltinDeclarationRanges(v___x_4184_, v___x_4185_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object* v_a_4187_){
_start:
{
lean_object* v_res_4188_; 
v_res_4188_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
return v_res_4188_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0));
v___x_4191_ = l_Lean_stringToMessageData(v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object* v___x_4192_, lean_object* v_declName_4193_, lean_object* v_type_4194_, lean_object* v_value_4195_, lean_object* v_rhs_4196_, lean_object* v_a_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_inc_ref(v_a_4197_);
v___x_4203_ = l_Lean_Expr_app___override(v___x_4192_, v_a_4197_);
lean_inc(v___y_4201_);
lean_inc_ref(v___y_4200_);
lean_inc(v___y_4199_);
lean_inc_ref(v___y_4198_);
v___x_4204_ = lean_infer_type(v___x_4203_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; uint8_t v___x_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc_n(v_a_4205_, 2);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = lean_unsigned_to_nat(1u);
v___x_4207_ = lean_mk_empty_array_with_capacity(v___x_4206_);
v___x_4208_ = lean_array_push(v___x_4207_, v_a_4197_);
v___x_4209_ = 0;
v___x_4210_ = 1;
v___x_4211_ = 1;
v___x_4212_ = l_Lean_Meta_mkLambdaFVars(v___x_4208_, v_a_4205_, v___x_4209_, v___x_4210_, v___x_4209_, v___x_4210_, v___x_4211_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
lean_inc(v_a_4205_);
v___x_4214_ = l_Lean_Meta_getLevel(v_a_4205_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v___x_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4216_, 0, v_a_4205_);
v___x_4217_ = 0;
v___x_4218_ = lean_box(0);
v___x_4219_ = l_Lean_Meta_mkFreshExprMVar(v___x_4216_, v___x_4217_, v___x_4218_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4221_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = l_Lean_Meta_mkLambdaFVars(v___x_4208_, v_a_4220_, v___x_4209_, v___x_4210_, v___x_4209_, v___x_4210_, v___x_4211_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
lean_dec_ref(v___x_4208_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4255_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4255_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4255_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4232_ = l_Lean_Expr_bindingBody_x21(v_a_4222_);
v___x_4233_ = l_Lean_Expr_letE___override(v_declName_4193_, v_type_4194_, v_value_4195_, v___x_4232_, v___x_4209_);
v___x_4234_ = l_Lean_Meta_isExprDefEq(v_rhs_4196_, v___x_4233_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v_a_4235_; uint8_t v___x_4236_; 
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v___x_4234_, 1);
v___x_4236_ = lean_unbox(v_a_4235_);
lean_dec(v_a_4235_);
if (v___x_4236_ == 0)
{
lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_del_object(v___x_4224_);
lean_dec(v_a_4222_);
lean_dec(v_a_4215_);
lean_dec(v_a_4213_);
v___x_4237_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1);
v___x_4238_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4237_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4238_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4238_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4238_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
else
{
goto v___jp_4226_;
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_del_object(v___x_4224_);
lean_dec(v_a_4222_);
lean_dec(v_a_4215_);
lean_dec(v_a_4213_);
v_a_4247_ = lean_ctor_get(v___x_4234_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4234_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4234_);
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
v___jp_4226_:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4227_, 0, v_a_4215_);
lean_ctor_set(v___x_4227_, 1, v_a_4222_);
v___x_4228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4228_, 0, v_a_4213_);
lean_ctor_set(v___x_4228_, 1, v___x_4227_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4228_);
v___x_4230_ = v___x_4224_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v_a_4215_);
lean_dec(v_a_4213_);
lean_dec_ref(v_rhs_4196_);
lean_dec_ref(v_value_4195_);
lean_dec_ref(v_type_4194_);
lean_dec(v_declName_4193_);
v_a_4256_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4221_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4221_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_a_4215_);
lean_dec(v_a_4213_);
lean_dec_ref(v___x_4208_);
lean_dec_ref(v_rhs_4196_);
lean_dec_ref(v_value_4195_);
lean_dec_ref(v_type_4194_);
lean_dec(v_declName_4193_);
v_a_4264_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4219_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4219_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v_a_4213_);
lean_dec_ref(v___x_4208_);
lean_dec(v_a_4205_);
lean_dec_ref(v_rhs_4196_);
lean_dec_ref(v_value_4195_);
lean_dec_ref(v_type_4194_);
lean_dec(v_declName_4193_);
v_a_4272_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4214_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4214_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v___x_4208_);
lean_dec(v_a_4205_);
lean_dec_ref(v_rhs_4196_);
lean_dec_ref(v_value_4195_);
lean_dec_ref(v_type_4194_);
lean_dec(v_declName_4193_);
v_a_4280_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4212_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4212_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
else
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4295_; 
lean_dec_ref(v_a_4197_);
lean_dec_ref(v_rhs_4196_);
lean_dec_ref(v_value_4195_);
lean_dec_ref(v_type_4194_);
lean_dec(v_declName_4193_);
v_a_4288_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_4290_ = v___x_4204_;
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4204_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4295_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4293_; 
if (v_isShared_4291_ == 0)
{
v___x_4293_ = v___x_4290_;
goto v_reusejp_4292_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
v___x_4293_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4292_;
}
v_reusejp_4292_:
{
return v___x_4293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object* v___x_4296_, lean_object* v_declName_4297_, lean_object* v_type_4298_, lean_object* v_value_4299_, lean_object* v_rhs_4300_, lean_object* v_a_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(v___x_4296_, v_declName_4297_, v_type_4298_, v_value_4299_, v_rhs_4300_, v_a_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object* v___x_4308_, lean_object* v_snd_4309_, lean_object* v_x_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4316_ = lean_unsigned_to_nat(1u);
v___x_4317_ = lean_mk_empty_array_with_capacity(v___x_4316_);
v___x_4318_ = lean_array_push(v___x_4317_, v_x_4310_);
lean_inc_ref_n(v___x_4318_, 2);
v___x_4319_ = l_Lean_Expr_beta(v___x_4308_, v___x_4318_);
v___x_4320_ = l_Lean_Expr_beta(v_snd_4309_, v___x_4318_);
v___x_4321_ = l_Lean_Meta_mkEq(v___x_4319_, v___x_4320_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
v___x_4323_ = lean_box(0);
v___x_4324_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4322_, v___x_4323_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; uint8_t v___x_4326_; uint8_t v___x_4327_; uint8_t v___x_4328_; lean_object* v___x_4329_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc_n(v_a_4325_, 2);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4326_ = 0;
v___x_4327_ = 1;
v___x_4328_ = 1;
v___x_4329_ = l_Lean_Meta_mkLambdaFVars(v___x_4318_, v_a_4325_, v___x_4326_, v___x_4327_, v___x_4326_, v___x_4327_, v___x_4328_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec_ref(v___x_4318_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4339_; 
v_a_4330_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4332_ = v___x_4329_;
v_isShared_4333_ = v_isSharedCheck_4339_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4329_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4339_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4337_; 
v___x_4334_ = l_Lean_Expr_mvarId_x21(v_a_4325_);
lean_dec(v_a_4325_);
v___x_4335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4335_, 0, v_a_4330_);
lean_ctor_set(v___x_4335_, 1, v___x_4334_);
if (v_isShared_4333_ == 0)
{
lean_ctor_set(v___x_4332_, 0, v___x_4335_);
v___x_4337_ = v___x_4332_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v___x_4335_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
else
{
lean_object* v_a_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
lean_dec(v_a_4325_);
v_a_4340_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4342_ = v___x_4329_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_a_4340_);
lean_dec(v___x_4329_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
lean_dec_ref(v___x_4318_);
v_a_4348_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4324_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4324_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
else
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
lean_dec_ref(v___x_4318_);
v_a_4356_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4321_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4321_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
return v___x_4361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object* v___x_4364_, lean_object* v_snd_4365_, lean_object* v_x_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(v___x_4364_, v_snd_4365_, v_x_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
return v_res_4372_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3(void){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2));
v___x_4378_ = l_Lean_stringToMessageData(v___x_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object* v_mvarId_4379_, lean_object* v_lhs_4380_, lean_object* v_rhs_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_){
_start:
{
if (lean_obj_tag(v_lhs_4380_) == 8)
{
lean_object* v_declName_4387_; lean_object* v_type_4388_; lean_object* v_value_4389_; lean_object* v_body_4390_; lean_object* v___x_4391_; 
v_declName_4387_ = lean_ctor_get(v_lhs_4380_, 0);
lean_inc(v_declName_4387_);
v_type_4388_ = lean_ctor_get(v_lhs_4380_, 1);
lean_inc_ref_n(v_type_4388_, 2);
v_value_4389_ = lean_ctor_get(v_lhs_4380_, 2);
lean_inc_ref(v_value_4389_);
v_body_4390_ = lean_ctor_get(v_lhs_4380_, 3);
lean_inc_ref(v_body_4390_);
lean_dec_ref_known(v_lhs_4380_, 4);
v___x_4391_ = l_Lean_Meta_getLevel(v_type_4388_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; uint8_t v___x_4393_; lean_object* v___x_4394_; lean_object* v___f_4395_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v___x_4472_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
v___x_4393_ = 0;
lean_inc_ref_n(v_type_4388_, 2);
lean_inc_n(v_declName_4387_, 2);
v___x_4394_ = l_Lean_mkLambda(v_declName_4387_, v___x_4393_, v_type_4388_, v_body_4390_);
lean_inc_ref(v_value_4389_);
lean_inc_ref_n(v___x_4394_, 2);
v___f_4395_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4395_, 0, v___x_4394_);
lean_closure_set(v___f_4395_, 1, v_declName_4387_);
lean_closure_set(v___f_4395_, 2, v_type_4388_);
lean_closure_set(v___f_4395_, 3, v_value_4389_);
lean_closure_set(v___f_4395_, 4, v_rhs_4381_);
v___x_4472_ = l_Lean_Meta_isTypeCorrect(v___x_4394_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; uint8_t v___x_4474_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v___x_4474_ = lean_unbox(v_a_4473_);
lean_dec(v_a_4473_);
if (v___x_4474_ == 0)
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec_ref(v___f_4395_);
lean_dec_ref(v___x_4394_);
lean_dec(v_a_4392_);
lean_dec_ref(v_value_4389_);
lean_dec_ref(v_type_4388_);
lean_dec(v_declName_4387_);
lean_dec(v_mvarId_4379_);
v___x_4475_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3);
v___x_4476_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4475_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
else
{
v___y_4397_ = v_a_4382_;
v___y_4398_ = v_a_4383_;
v___y_4399_ = v_a_4384_;
v___y_4400_ = v_a_4385_;
goto v___jp_4396_;
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
lean_dec_ref(v___f_4395_);
lean_dec_ref(v___x_4394_);
lean_dec(v_a_4392_);
lean_dec_ref(v_value_4389_);
lean_dec_ref(v_type_4388_);
lean_dec(v_declName_4387_);
lean_dec(v_mvarId_4379_);
v_a_4485_ = lean_ctor_get(v___x_4472_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4472_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4472_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
v___jp_4396_:
{
lean_object* v___x_4401_; 
lean_inc_ref(v_type_4388_);
lean_inc(v_declName_4387_);
v___x_4401_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4387_, v_type_4388_, v___f_4395_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; lean_object* v_snd_4403_; lean_object* v_fst_4404_; lean_object* v_fst_4405_; lean_object* v_snd_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4463_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v_snd_4403_ = lean_ctor_get(v_a_4402_, 1);
lean_inc(v_snd_4403_);
v_fst_4404_ = lean_ctor_get(v_a_4402_, 0);
lean_inc(v_fst_4404_);
lean_dec(v_a_4402_);
v_fst_4405_ = lean_ctor_get(v_snd_4403_, 0);
v_snd_4406_ = lean_ctor_get(v_snd_4403_, 1);
v_isSharedCheck_4463_ = !lean_is_exclusive(v_snd_4403_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4408_ = v_snd_4403_;
v_isShared_4409_ = v_isSharedCheck_4463_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_snd_4406_);
lean_inc(v_fst_4405_);
lean_dec(v_snd_4403_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4463_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___f_4410_; lean_object* v___x_4411_; 
lean_inc(v_snd_4406_);
lean_inc_ref(v___x_4394_);
v___f_4410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4410_, 0, v___x_4394_);
lean_closure_set(v___f_4410_, 1, v_snd_4406_);
lean_inc_ref(v_type_4388_);
v___x_4411_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4387_, v_type_4388_, v___f_4410_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v_fst_4413_; lean_object* v_snd_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4454_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v_fst_4413_ = lean_ctor_get(v_a_4412_, 0);
v_snd_4414_ = lean_ctor_get(v_a_4412_, 1);
v_isSharedCheck_4454_ = !lean_is_exclusive(v_a_4412_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4416_ = v_a_4412_;
v_isShared_4417_ = v_isSharedCheck_4454_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_snd_4414_);
lean_inc(v_fst_4413_);
lean_dec(v_a_4412_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4454_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4421_; 
v___x_4418_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1));
v___x_4419_ = lean_box(0);
if (v_isShared_4417_ == 0)
{
lean_ctor_set_tag(v___x_4416_, 1);
lean_ctor_set(v___x_4416_, 1, v___x_4419_);
lean_ctor_set(v___x_4416_, 0, v_fst_4405_);
v___x_4421_ = v___x_4416_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_fst_4405_);
lean_ctor_set(v_reuseFailAlloc_4453_, 1, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4423_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set_tag(v___x_4408_, 1);
lean_ctor_set(v___x_4408_, 1, v___x_4421_);
lean_ctor_set(v___x_4408_, 0, v_a_4392_);
v___x_4423_ = v___x_4408_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4392_);
lean_ctor_set(v_reuseFailAlloc_4452_, 1, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4450_; 
v___x_4424_ = l_Lean_mkConst(v___x_4418_, v___x_4423_);
v___x_4425_ = l_Lean_mkApp6(v___x_4424_, v_type_4388_, v_fst_4404_, v___x_4394_, v_snd_4406_, v_value_4389_, v_fst_4413_);
v___x_4426_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4379_, v___x_4425_, v___y_4398_);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4450_ == 0)
{
lean_object* v_unused_4451_; 
v_unused_4451_ = lean_ctor_get(v___x_4426_, 0);
lean_dec(v_unused_4451_);
v___x_4428_ = v___x_4426_;
v_isShared_4429_ = v_isSharedCheck_4450_;
goto v_resetjp_4427_;
}
else
{
lean_dec(v___x_4426_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4450_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4414_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4441_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4441_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4441_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set_tag(v___x_4428_, 1);
lean_ctor_set(v___x_4428_, 0, v_a_4431_);
v___x_4436_ = v___x_4428_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4438_; 
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4436_);
v___x_4438_ = v___x_4433_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_del_object(v___x_4428_);
v_a_4442_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4430_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4430_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
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
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_del_object(v___x_4408_);
lean_dec(v_snd_4406_);
lean_dec(v_fst_4405_);
lean_dec(v_fst_4404_);
lean_dec_ref(v___x_4394_);
lean_dec(v_a_4392_);
lean_dec_ref(v_value_4389_);
lean_dec_ref(v_type_4388_);
lean_dec(v_mvarId_4379_);
v_a_4455_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4411_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4411_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4471_; 
lean_dec_ref(v___x_4394_);
lean_dec(v_a_4392_);
lean_dec_ref(v_value_4389_);
lean_dec_ref(v_type_4388_);
lean_dec(v_declName_4387_);
lean_dec(v_mvarId_4379_);
v_a_4464_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4471_ == 0)
{
v___x_4466_ = v___x_4401_;
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
else
{
lean_inc(v_a_4464_);
lean_dec(v___x_4401_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4471_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v___x_4469_; 
if (v_isShared_4467_ == 0)
{
v___x_4469_ = v___x_4466_;
goto v_reusejp_4468_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_a_4464_);
v___x_4469_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4468_;
}
v_reusejp_4468_:
{
return v___x_4469_;
}
}
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec_ref(v_body_4390_);
lean_dec_ref(v_value_4389_);
lean_dec_ref(v_type_4388_);
lean_dec(v_declName_4387_);
lean_dec_ref(v_rhs_4381_);
lean_dec(v_mvarId_4379_);
v_a_4493_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4391_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4391_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
else
{
lean_object* v___x_4501_; lean_object* v___x_4502_; 
lean_dec_ref(v_rhs_4381_);
lean_dec_ref(v_lhs_4380_);
lean_dec(v_mvarId_4379_);
v___x_4501_ = lean_box(0);
v___x_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4502_, 0, v___x_4501_);
return v___x_4502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object* v_mvarId_4503_, lean_object* v_lhs_4504_, lean_object* v_rhs_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4503_, v_lhs_4504_, v_rhs_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec_ref(v_a_4506_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object* v_body_4513_, lean_object* v_snd_4514_, lean_object* v_b_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = lean_expr_instantiate1(v_body_4513_, v_b_4515_);
v___x_4522_ = lean_box(0);
v___x_4523_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_4521_, v___x_4522_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; lean_object* v_fst_4525_; lean_object* v_snd_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4588_; 
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4524_);
lean_dec_ref_known(v___x_4523_, 1);
v_fst_4525_ = lean_ctor_get(v_a_4524_, 0);
v_snd_4526_ = lean_ctor_get(v_a_4524_, 1);
v_isSharedCheck_4588_ = !lean_is_exclusive(v_a_4524_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4528_ = v_a_4524_;
v_isShared_4529_ = v_isSharedCheck_4588_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_snd_4526_);
lean_inc(v_fst_4525_);
lean_dec(v_a_4524_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4588_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; uint8_t v___x_4533_; uint8_t v___x_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; 
v___x_4530_ = lean_unsigned_to_nat(1u);
v___x_4531_ = lean_mk_empty_array_with_capacity(v___x_4530_);
v___x_4532_ = lean_array_push(v___x_4531_, v_b_4515_);
v___x_4533_ = 0;
v___x_4534_ = 1;
v___x_4535_ = 1;
lean_inc(v_fst_4525_);
v___x_4536_ = l_Lean_Meta_mkLambdaFVars(v___x_4532_, v_fst_4525_, v___x_4533_, v___x_4534_, v___x_4533_, v___x_4534_, v___x_4535_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
lean_inc(v_snd_4526_);
v___x_4538_ = l_Lean_Meta_mkLambdaFVars(v___x_4532_, v_snd_4526_, v___x_4533_, v___x_4534_, v___x_4533_, v___x_4534_, v___x_4535_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v___x_4540_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v___x_4540_ = l_Lean_Meta_mkForallFVars(v___x_4532_, v_fst_4525_, v___x_4533_, v___x_4534_, v___x_4534_, v___x_4535_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec_ref(v___x_4532_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref_known(v___x_4540_, 1);
v___x_4542_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_4543_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_4542_, v_snd_4514_, v_a_4541_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4554_; 
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v___x_4543_, 0);
lean_dec(v_unused_4555_);
v___x_4545_ = v___x_4543_;
v_isShared_4546_ = v_isSharedCheck_4554_;
goto v_resetjp_4544_;
}
else
{
lean_dec(v___x_4543_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4554_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v_a_4539_);
v___x_4548_ = v___x_4528_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4539_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_snd_4526_);
v___x_4548_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
lean_object* v___x_4549_; lean_object* v___x_4551_; 
v___x_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4549_, 0, v_a_4537_);
lean_ctor_set(v___x_4549_, 1, v___x_4548_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v___x_4549_);
v___x_4551_ = v___x_4545_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v___x_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v_a_4539_);
lean_dec(v_a_4537_);
lean_del_object(v___x_4528_);
lean_dec(v_snd_4526_);
v_a_4556_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4543_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4543_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec(v_a_4539_);
lean_dec(v_a_4537_);
lean_del_object(v___x_4528_);
lean_dec(v_snd_4526_);
lean_dec_ref(v_snd_4514_);
v_a_4564_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4540_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4540_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec(v_a_4537_);
lean_dec_ref(v___x_4532_);
lean_del_object(v___x_4528_);
lean_dec(v_snd_4526_);
lean_dec(v_fst_4525_);
lean_dec_ref(v_snd_4514_);
v_a_4572_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4538_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4538_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec_ref(v___x_4532_);
lean_del_object(v___x_4528_);
lean_dec(v_snd_4526_);
lean_dec(v_fst_4525_);
lean_dec_ref(v_snd_4514_);
v_a_4580_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4536_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4536_);
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
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec_ref(v_b_4515_);
lean_dec_ref(v_snd_4514_);
v_a_4589_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4523_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4523_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object* v_body_4597_, lean_object* v_snd_4598_, lean_object* v_b_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(v_body_4597_, v_snd_4598_, v_b_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec_ref(v_body_4597_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object* v_body_4606_, lean_object* v_snd_4607_, lean_object* v_name_4608_, uint8_t v_bi_4609_, lean_object* v_type_4610_, uint8_t v_kind_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v___f_4617_; lean_object* v___x_4618_; 
v___f_4617_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4617_, 0, v_body_4606_);
lean_closure_set(v___f_4617_, 1, v_snd_4607_);
v___x_4618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4608_, v_bi_4609_, v_type_4610_, v___f_4617_, v_kind_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4618_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4618_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
else
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4634_; 
v_a_4627_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4629_ = v___x_4618_;
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4618_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4634_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object* v_body_4635_, lean_object* v_snd_4636_, lean_object* v_name_4637_, lean_object* v_bi_4638_, lean_object* v_type_4639_, lean_object* v_kind_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
uint8_t v_bi_boxed_4646_; uint8_t v_kind_boxed_4647_; lean_object* v_res_4648_; 
v_bi_boxed_4646_ = lean_unbox(v_bi_4638_);
v_kind_boxed_4647_ = lean_unbox(v_kind_4640_);
v_res_4648_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4635_, v_snd_4636_, v_name_4637_, v_bi_boxed_4646_, v_type_4639_, v_kind_boxed_4647_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
return v_res_4648_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4650_; lean_object* v___x_4651_; 
v___x_4650_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0));
v___x_4651_ = l_Lean_stringToMessageData(v___x_4650_);
return v___x_4651_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6));
v___x_4660_ = l_Lean_stringToMessageData(v___x_4659_);
return v___x_4660_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8));
v___x_4663_ = l_Lean_stringToMessageData(v___x_4662_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object* v_mvarId_4664_, lean_object* v_userName_x3f_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; uint8_t v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___x_4738_; 
lean_inc(v_mvarId_4664_);
v___x_4738_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_4664_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
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
v___x_4745_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_4740_, v___y_4667_);
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
v___x_4752_ = l_Lean_Meta_getLevel(v_binderType_4749_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
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
if (lean_obj_tag(v_userName_x3f_4665_) == 1)
{
lean_object* v_val_4797_; 
lean_dec(v_binderName_4748_);
v_val_4797_ = lean_ctor_get(v_userName_x3f_4665_, 0);
lean_inc(v_val_4797_);
lean_dec_ref_known(v_userName_x3f_4665_, 1);
v_userName_4756_ = v_val_4797_;
v___y_4757_ = v___y_4666_;
v___y_4758_ = v___y_4667_;
v___y_4759_ = v___y_4668_;
v___y_4760_ = v___y_4669_;
goto v___jp_4755_;
}
else
{
lean_object* v___x_4798_; 
lean_dec(v_userName_x3f_4665_);
v___x_4798_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_4748_, v___y_4666_, v___y_4668_, v___y_4669_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
v_userName_4756_ = v_a_4799_;
v___y_4757_ = v___y_4666_;
v___y_4758_ = v___y_4667_;
v___y_4759_ = v___y_4668_;
v___y_4760_ = v___y_4669_;
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
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_mvarId_4664_);
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
v___x_4777_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4664_, v___x_4776_, v___y_4758_);
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
lean_dec(v_mvarId_4664_);
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
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
lean_inc(v_mvarId_4664_);
v___x_4816_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4664_, v___x_4747_, v_snd_4741_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
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
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
lean_inc(v___y_4669_);
lean_inc_ref(v___y_4668_);
lean_inc(v___y_4667_);
lean_inc_ref(v___y_4666_);
lean_inc_ref(v___x_4747_);
v___x_4825_ = lean_infer_type(v___x_4747_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
if (lean_obj_tag(v___x_4825_) == 0)
{
lean_object* v_a_4826_; lean_object* v___x_4827_; 
v_a_4826_ = lean_ctor_get(v___x_4825_, 0);
lean_inc(v_a_4826_);
lean_dec_ref_known(v___x_4825_, 1);
v___x_4827_ = l_Lean_Meta_whnfD(v_a_4826_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
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
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
v___x_4839_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4838_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
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
goto v___jp_4699_;
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_dec_ref(v___x_4747_);
lean_del_object(v___x_4743_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
v___jp_4671_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1);
v___x_4677_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4676_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
return v___x_4677_;
}
v___jp_4678_:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4686_ = lean_unsigned_to_nat(1u);
v___x_4687_ = l_Lean_Meta_introNCore(v___y_4681_, v___x_4686_, v___y_4685_, v___y_4683_, v___y_4683_, v___y_4680_, v___y_4682_, v___y_4679_, v___y_4684_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v_snd_4689_; lean_object* v___x_4690_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v___x_4687_, 1);
v_snd_4689_ = lean_ctor_get(v_a_4688_, 1);
lean_inc(v_snd_4689_);
lean_dec(v_a_4688_);
v___x_4690_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4689_, v___y_4680_, v___y_4682_, v___y_4679_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4680_);
return v___x_4690_;
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_dec(v___y_4684_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4680_);
lean_dec_ref(v___y_4679_);
v_a_4691_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4687_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4687_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
v___jp_4699_:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3));
v___x_4701_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_4700_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_object* v_a_4702_; uint8_t v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
lean_inc(v_a_4702_);
lean_dec_ref_known(v___x_4701_, 1);
v___x_4703_ = 0;
v___x_4704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4));
v___x_4705_ = lean_box(0);
v___x_4706_ = l_Lean_MVarId_apply(v_mvarId_4664_, v_a_4702_, v___x_4704_, v___x_4705_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
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
if (lean_obj_tag(v_userName_x3f_4665_) == 1)
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
v_val_4713_ = lean_ctor_get(v_userName_x3f_4665_, 0);
lean_inc(v_val_4713_);
lean_dec_ref_known(v_userName_x3f_4665_, 1);
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
v___y_4679_ = v___y_4668_;
v___y_4680_ = v___y_4666_;
v___y_4681_ = v_head_4709_;
v___y_4682_ = v___y_4667_;
v___y_4683_ = v___x_4703_;
v___y_4684_ = v___y_4669_;
v___y_4685_ = v___x_4716_;
goto v___jp_4678_;
}
}
}
else
{
lean_object* v_head_4720_; lean_object* v___x_4721_; 
lean_dec(v_userName_x3f_4665_);
v_head_4720_ = lean_ctor_get(v_a_4707_, 0);
lean_inc(v_head_4720_);
lean_dec_ref_known(v_a_4707_, 2);
v___x_4721_ = lean_box(0);
v___y_4679_ = v___y_4668_;
v___y_4680_ = v___y_4666_;
v___y_4681_ = v_head_4720_;
v___y_4682_ = v___y_4667_;
v___y_4683_ = v___x_4703_;
v___y_4684_ = v___y_4669_;
v___y_4685_ = v___x_4721_;
goto v___jp_4678_;
}
}
else
{
lean_dec_ref_known(v_a_4707_, 2);
lean_dec(v_userName_x3f_4665_);
v___y_4672_ = v___y_4666_;
v___y_4673_ = v___y_4667_;
v___y_4674_ = v___y_4668_;
v___y_4675_ = v___y_4669_;
goto v___jp_4671_;
}
}
else
{
lean_dec(v_a_4707_);
lean_dec(v_userName_x3f_4665_);
v___y_4672_ = v___y_4666_;
v___y_4673_ = v___y_4667_;
v___y_4674_ = v___y_4668_;
v___y_4675_ = v___y_4669_;
goto v___jp_4671_;
}
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
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
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v_userName_x3f_4665_);
lean_dec(v_mvarId_4664_);
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
lean_object* v___x_4987_; lean_object* v_a_4988_; lean_object* v___y_4990_; lean_object* v___x_5003_; uint8_t v___x_5004_; 
v___x_4987_ = lean_box(0);
v_a_4988_ = lean_array_uget_borrowed(v_as_4975_, v_i_4977_);
v___x_5003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1));
lean_inc(v_a_4988_);
v___x_5004_ = l_Lean_Syntax_isOfKind(v_a_4988_, v___x_5003_);
if (v___x_5004_ == 0)
{
lean_object* v___x_5005_; 
v___x_5005_ = lean_box(0);
v___y_4990_ = v___x_5005_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; uint8_t v___x_5009_; 
v___x_5006_ = lean_unsigned_to_nat(0u);
v___x_5007_ = l_Lean_Syntax_getArg(v_a_4988_, v___x_5006_);
v___x_5008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3));
lean_inc(v___x_5007_);
v___x_5009_ = l_Lean_Syntax_isOfKind(v___x_5007_, v___x_5008_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; 
lean_dec(v___x_5007_);
v___x_5010_ = lean_box(0);
v___y_4990_ = v___x_5010_;
goto v___jp_4989_;
}
else
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = l_Lean_TSyntax_getId(v___x_5007_);
lean_dec(v___x_5007_);
v___x_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
v___y_4990_ = v___x_5012_;
goto v___jp_4989_;
}
}
v___jp_4989_:
{
lean_object* v_toCold_4991_; lean_object* v_currRecDepth_4992_; lean_object* v_ref_4993_; uint16_t v_optionFlags_4994_; uint8_t v_suppressElabErrors_4995_; uint8_t v_isRecordingDeps_4996_; lean_object* v_ref_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v_toCold_4991_ = lean_ctor_get(v___y_4982_, 0);
v_currRecDepth_4992_ = lean_ctor_get(v___y_4982_, 1);
v_ref_4993_ = lean_ctor_get(v___y_4982_, 2);
v_optionFlags_4994_ = lean_ctor_get_uint16(v___y_4982_, sizeof(void*)*3);
v_suppressElabErrors_4995_ = lean_ctor_get_uint8(v___y_4982_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4996_ = lean_ctor_get_uint8(v___y_4982_, sizeof(void*)*3 + 3);
v_ref_4997_ = l_Lean_replaceRef(v_a_4988_, v_ref_4993_);
lean_inc(v_currRecDepth_4992_);
lean_inc_ref(v_toCold_4991_);
v___x_4998_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4998_, 0, v_toCold_4991_);
lean_ctor_set(v___x_4998_, 1, v_currRecDepth_4992_);
lean_ctor_set(v___x_4998_, 2, v_ref_4997_);
lean_ctor_set_uint16(v___x_4998_, sizeof(void*)*3, v_optionFlags_4994_);
lean_ctor_set_uint8(v___x_4998_, sizeof(void*)*3 + 2, v_suppressElabErrors_4995_);
lean_ctor_set_uint8(v___x_4998_, sizeof(void*)*3 + 3, v_isRecordingDeps_4996_);
v___x_4999_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___y_4990_, v___y_4979_, v___y_4980_, v___y_4981_, v___x_4998_, v___y_4983_);
lean_dec_ref_known(v___x_4998_, 3);
if (lean_obj_tag(v___x_4999_) == 0)
{
size_t v___x_5000_; size_t v___x_5001_; 
lean_dec_ref_known(v___x_4999_, 1);
v___x_5000_ = ((size_t)1ULL);
v___x_5001_ = lean_usize_add(v_i_4977_, v___x_5000_);
v_i_4977_ = v___x_5001_;
v_b_4978_ = v___x_4987_;
goto _start;
}
else
{
return v___x_4999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object* v_as_5013_, lean_object* v_sz_5014_, lean_object* v_i_5015_, lean_object* v_b_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
size_t v_sz_boxed_5023_; size_t v_i_boxed_5024_; lean_object* v_res_5025_; 
v_sz_boxed_5023_ = lean_unbox_usize(v_sz_5014_);
lean_dec(v_sz_5014_);
v_i_boxed_5024_ = lean_unbox_usize(v_i_5015_);
lean_dec(v_i_5015_);
v_res_5025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5013_, v_sz_boxed_5023_, v_i_boxed_5024_, v_b_5016_, v___y_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v_as_5013_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object* v_stx_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v_ids_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; 
v___x_5036_ = lean_unsigned_to_nat(1u);
v___x_5037_ = l_Lean_Syntax_getArg(v_stx_5026_, v___x_5036_);
v_ids_5038_ = l_Lean_Syntax_getArgs(v___x_5037_);
lean_dec(v___x_5037_);
v___x_5039_ = lean_array_get_size(v_ids_5038_);
v___x_5040_ = lean_unsigned_to_nat(0u);
v___x_5041_ = lean_nat_dec_eq(v___x_5039_, v___x_5040_);
if (v___x_5041_ == 0)
{
lean_object* v___x_5042_; size_t v_sz_5043_; size_t v___x_5044_; lean_object* v___x_5045_; 
v___x_5042_ = lean_box(0);
v_sz_5043_ = lean_array_size(v_ids_5038_);
v___x_5044_ = ((size_t)0ULL);
v___x_5045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_ids_5038_, v_sz_5043_, v___x_5044_, v___x_5042_, v_a_5028_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
lean_dec_ref(v_ids_5038_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5052_ == 0)
{
lean_object* v_unused_5053_; 
v_unused_5053_ = lean_ctor_get(v___x_5045_, 0);
lean_dec(v_unused_5053_);
v___x_5047_ = v___x_5045_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_dec(v___x_5045_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v___x_5042_);
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5042_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
else
{
return v___x_5045_;
}
}
else
{
lean_object* v___x_5054_; lean_object* v___x_5055_; 
lean_dec_ref(v_ids_5038_);
v___x_5054_ = lean_box(0);
v___x_5055_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___x_5054_, v_a_5028_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object* v_stx_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_){
_start:
{
lean_object* v_res_5066_; 
v_res_5066_ = l_Lean_Elab_Tactic_Conv_evalExt(v_stx_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_);
lean_dec(v_a_5064_);
lean_dec_ref(v_a_5063_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
lean_dec(v_stx_5056_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object* v_as_5067_, size_t v_sz_5068_, size_t v_i_5069_, lean_object* v_b_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v___x_5080_; 
v___x_5080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5067_, v_sz_5068_, v_i_5069_, v_b_5070_, v___y_5072_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
return v___x_5080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object* v_as_5081_, lean_object* v_sz_5082_, lean_object* v_i_5083_, lean_object* v_b_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
size_t v_sz_boxed_5094_; size_t v_i_boxed_5095_; lean_object* v_res_5096_; 
v_sz_boxed_5094_ = lean_unbox_usize(v_sz_5082_);
lean_dec(v_sz_5082_);
v_i_boxed_5095_ = lean_unbox_usize(v_i_5083_);
lean_dec(v_i_5083_);
v_res_5096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(v_as_5081_, v_sz_boxed_5094_, v_i_boxed_5095_, v_b_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
lean_dec(v___y_5090_);
lean_dec_ref(v___y_5089_);
lean_dec(v___y_5088_);
lean_dec_ref(v___y_5087_);
lean_dec(v___y_5086_);
lean_dec_ref(v___y_5085_);
lean_dec_ref(v_as_5081_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1(){
_start:
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
v___x_5111_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0));
v___x_5113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5114_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExt___boxed), 10, 0);
v___x_5115_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5111_, v___x_5112_, v___x_5113_, v___x_5114_);
return v___x_5115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object* v_a_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3(){
_start:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
v___x_5144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6));
v___x_5146_ = l_Lean_addBuiltinDeclarationRanges(v___x_5144_, v___x_5145_);
return v___x_5146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object* v_a_5147_){
_start:
{
lean_object* v_res_5148_; 
v_res_5148_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object* v___x_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_){
_start:
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5149_);
return v___x_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object* v___x_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_){
_start:
{
lean_object* v_res_5170_; 
v_res_5170_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(v___x_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_, v___y_5168_);
lean_dec(v___y_5168_);
lean_dec_ref(v___y_5167_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object* v_a_5171_, lean_object* v_trees_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v___x_5182_; 
lean_inc(v___y_5180_);
lean_inc_ref(v___y_5179_);
lean_inc(v___y_5178_);
lean_inc_ref(v___y_5177_);
lean_inc(v___y_5176_);
lean_inc_ref(v___y_5175_);
lean_inc(v___y_5174_);
lean_inc_ref(v___y_5173_);
v___x_5182_ = lean_apply_9(v_a_5171_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, lean_box(0));
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5191_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5185_ = v___x_5182_;
v_isShared_5186_ = v_isSharedCheck_5191_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5182_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5191_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5187_; lean_object* v___x_5189_; 
v___x_5187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5187_, 0, v_a_5183_);
lean_ctor_set(v___x_5187_, 1, v_trees_5172_);
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 0, v___x_5187_);
v___x_5189_ = v___x_5185_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5187_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
else
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5199_; 
lean_dec_ref(v_trees_5172_);
v_a_5192_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5194_ = v___x_5182_;
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_5182_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5197_; 
if (v_isShared_5195_ == 0)
{
v___x_5197_ = v___x_5194_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_a_5192_);
v___x_5197_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
return v___x_5197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object* v_a_5200_, lean_object* v_trees_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(v_a_5200_, v_trees_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
lean_dec(v___y_5209_);
lean_dec_ref(v___y_5208_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec(v___y_5203_);
lean_dec_ref(v___y_5202_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(lean_object* v_a_5212_, lean_object* v_trees_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_){
_start:
{
lean_object* v___x_5223_; 
lean_inc(v___y_5221_);
lean_inc_ref(v___y_5220_);
lean_inc(v___y_5219_);
lean_inc_ref(v___y_5218_);
lean_inc(v___y_5217_);
lean_inc_ref(v___y_5216_);
lean_inc(v___y_5215_);
lean_inc_ref(v___y_5214_);
v___x_5223_ = lean_apply_9(v_a_5212_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_, v___y_5220_, v___y_5221_, lean_box(0));
if (lean_obj_tag(v___x_5223_) == 0)
{
lean_object* v_a_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5232_; 
v_a_5224_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5226_ = v___x_5223_;
v_isShared_5227_ = v_isSharedCheck_5232_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_a_5224_);
lean_dec(v___x_5223_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5232_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5228_; lean_object* v___x_5230_; 
v___x_5228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5228_, 0, v_a_5224_);
lean_ctor_set(v___x_5228_, 1, v_trees_5213_);
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 0, v___x_5228_);
v___x_5230_ = v___x_5226_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v___x_5228_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
else
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5240_; 
lean_dec_ref(v_trees_5213_);
v_a_5233_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5235_ = v___x_5223_;
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5223_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5240_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5238_; 
if (v_isShared_5236_ == 0)
{
v___x_5238_ = v___x_5235_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v_a_5233_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object* v_a_5241_, lean_object* v_trees_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(v_a_5241_, v_trees_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___y_5248_);
lean_dec_ref(v___y_5247_);
lean_dec(v___y_5246_);
lean_dec_ref(v___y_5245_);
lean_dec(v___y_5244_);
lean_dec_ref(v___y_5243_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(uint8_t v___x_5253_, lean_object* v___x_5254_, lean_object* v___x_5255_, lean_object* v___x_5256_, lean_object* v___x_5257_, lean_object* v___x_5258_, lean_object* v___x_5259_, lean_object* v___x_5260_, lean_object* v___x_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
if (v___x_5253_ == 0)
{
lean_object* v___x_5271_; 
lean_dec_ref(v___y_5268_);
lean_dec(v___x_5261_);
lean_dec_ref(v___x_5260_);
lean_dec_ref(v___x_5259_);
lean_dec_ref(v___x_5258_);
lean_dec_ref(v___x_5257_);
v___x_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5271_, 0, v___x_5254_);
return v___x_5271_;
}
else
{
lean_object* v_toCold_5272_; lean_object* v_currRecDepth_5273_; lean_object* v_ref_5274_; uint16_t v_optionFlags_5275_; uint8_t v_suppressElabErrors_5276_; uint8_t v_isRecordingDeps_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5307_; 
v_toCold_5272_ = lean_ctor_get(v___y_5268_, 0);
v_currRecDepth_5273_ = lean_ctor_get(v___y_5268_, 1);
v_ref_5274_ = lean_ctor_get(v___y_5268_, 2);
v_optionFlags_5275_ = lean_ctor_get_uint16(v___y_5268_, sizeof(void*)*3);
v_suppressElabErrors_5276_ = lean_ctor_get_uint8(v___y_5268_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5277_ = lean_ctor_get_uint8(v___y_5268_, sizeof(void*)*3 + 3);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___y_5268_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5279_ = v___y_5268_;
v_isShared_5280_ = v_isSharedCheck_5307_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_ref_5274_);
lean_inc(v_currRecDepth_5273_);
lean_inc(v_toCold_5272_);
lean_dec(v___y_5268_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5307_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_ref_5281_; lean_object* v___x_5283_; 
v_ref_5281_ = l_Lean_replaceRef(v___x_5255_, v_ref_5274_);
lean_dec(v_ref_5274_);
lean_inc(v_ref_5281_);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 2, v_ref_5281_);
v___x_5283_ = v___x_5279_;
goto v_reusejp_5282_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_toCold_5272_);
lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_currRecDepth_5273_);
lean_ctor_set(v_reuseFailAlloc_5306_, 2, v_ref_5281_);
lean_ctor_set_uint16(v_reuseFailAlloc_5306_, sizeof(void*)*3, v_optionFlags_5275_);
lean_ctor_set_uint8(v_reuseFailAlloc_5306_, sizeof(void*)*3 + 2, v_suppressElabErrors_5276_);
lean_ctor_set_uint8(v_reuseFailAlloc_5306_, sizeof(void*)*3 + 3, v_isRecordingDeps_5277_);
v___x_5283_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5282_;
}
v_reusejp_5282_:
{
lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; uint8_t v___x_5287_; 
v___x_5284_ = l_Lean_Syntax_getArg(v___x_5255_, v___x_5256_);
v___x_5285_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__2));
lean_inc_ref(v___x_5260_);
lean_inc_ref(v___x_5259_);
lean_inc_ref(v___x_5258_);
lean_inc_ref(v___x_5257_);
v___x_5286_ = l_Lean_Name_mkStr5(v___x_5257_, v___x_5258_, v___x_5259_, v___x_5260_, v___x_5285_);
lean_inc(v___x_5284_);
v___x_5287_ = l_Lean_Syntax_isOfKind(v___x_5284_, v___x_5286_);
lean_dec(v___x_5286_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; 
v___x_5288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0));
lean_inc_ref(v___x_5257_);
v___x_5289_ = l_Lean_Name_mkStr2(v___x_5257_, v___x_5288_);
lean_inc(v___x_5284_);
v___x_5290_ = l_Lean_Syntax_isOfKind(v___x_5284_, v___x_5289_);
lean_dec(v___x_5289_);
if (v___x_5290_ == 0)
{
lean_object* v___x_5291_; 
lean_dec(v___x_5284_);
lean_dec_ref(v___x_5283_);
lean_dec(v_ref_5281_);
lean_dec(v___x_5261_);
lean_dec_ref(v___x_5260_);
lean_dec_ref(v___x_5259_);
lean_dec_ref(v___x_5258_);
lean_dec_ref(v___x_5257_);
v___x_5291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5291_, 0, v___x_5254_);
return v___x_5291_;
}
else
{
lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5292_ = l_Lean_SourceInfo_fromRef(v_ref_5281_, v___x_5287_);
lean_dec(v_ref_5281_);
v___x_5293_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_5294_ = l_Lean_Name_mkStr5(v___x_5257_, v___x_5258_, v___x_5259_, v___x_5260_, v___x_5293_);
lean_inc_n(v___x_5292_, 2);
v___x_5295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5295_, 0, v___x_5292_);
lean_ctor_set(v___x_5295_, 1, v___x_5293_);
v___x_5296_ = l_Lean_Syntax_node1(v___x_5292_, v___x_5261_, v___x_5284_);
v___x_5297_ = l_Lean_Syntax_node2(v___x_5292_, v___x_5294_, v___x_5295_, v___x_5296_);
v___x_5298_ = l_Lean_Elab_Tactic_evalTactic(v___x_5297_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___x_5283_, v___y_5269_);
lean_dec_ref(v___x_5283_);
return v___x_5298_;
}
}
else
{
uint8_t v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; 
lean_dec(v___x_5261_);
v___x_5299_ = 0;
v___x_5300_ = l_Lean_SourceInfo_fromRef(v_ref_5281_, v___x_5299_);
lean_dec(v_ref_5281_);
v___x_5301_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_5302_ = l_Lean_Name_mkStr5(v___x_5257_, v___x_5258_, v___x_5259_, v___x_5260_, v___x_5301_);
lean_inc(v___x_5300_);
v___x_5303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5303_, 0, v___x_5300_);
lean_ctor_set(v___x_5303_, 1, v___x_5301_);
v___x_5304_ = l_Lean_Syntax_node2(v___x_5300_, v___x_5302_, v___x_5303_, v___x_5284_);
v___x_5305_ = l_Lean_Elab_Tactic_evalTactic(v___x_5304_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___x_5283_, v___y_5269_);
lean_dec_ref(v___x_5283_);
return v___x_5305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5308_ = _args[0];
lean_object* v___x_5309_ = _args[1];
lean_object* v___x_5310_ = _args[2];
lean_object* v___x_5311_ = _args[3];
lean_object* v___x_5312_ = _args[4];
lean_object* v___x_5313_ = _args[5];
lean_object* v___x_5314_ = _args[6];
lean_object* v___x_5315_ = _args[7];
lean_object* v___x_5316_ = _args[8];
lean_object* v___y_5317_ = _args[9];
lean_object* v___y_5318_ = _args[10];
lean_object* v___y_5319_ = _args[11];
lean_object* v___y_5320_ = _args[12];
lean_object* v___y_5321_ = _args[13];
lean_object* v___y_5322_ = _args[14];
lean_object* v___y_5323_ = _args[15];
lean_object* v___y_5324_ = _args[16];
lean_object* v___y_5325_ = _args[17];
_start:
{
uint8_t v___x_15769__boxed_5326_; lean_object* v_res_5327_; 
v___x_15769__boxed_5326_ = lean_unbox(v___x_5308_);
v_res_5327_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(v___x_15769__boxed_5326_, v___x_5309_, v___x_5310_, v___x_5311_, v___x_5312_, v___x_5313_, v___x_5314_, v___x_5315_, v___x_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
lean_dec(v___y_5324_);
lean_dec(v___y_5322_);
lean_dec_ref(v___y_5321_);
lean_dec(v___y_5320_);
lean_dec_ref(v___y_5319_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v___x_5311_);
lean_dec(v___x_5310_);
return v_res_5327_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5328_ = lean_unsigned_to_nat(32u);
v___x_5329_ = lean_mk_empty_array_with_capacity(v___x_5328_);
v___x_5330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5329_);
return v___x_5330_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; 
v___x_5331_ = ((size_t)5ULL);
v___x_5332_ = lean_unsigned_to_nat(0u);
v___x_5333_ = lean_unsigned_to_nat(32u);
v___x_5334_ = lean_mk_empty_array_with_capacity(v___x_5333_);
v___x_5335_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0);
v___x_5336_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5336_, 0, v___x_5335_);
lean_ctor_set(v___x_5336_, 1, v___x_5334_);
lean_ctor_set(v___x_5336_, 2, v___x_5332_);
lean_ctor_set(v___x_5336_, 3, v___x_5332_);
lean_ctor_set_usize(v___x_5336_, 4, v___x_5331_);
return v___x_5336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object* v___y_5337_){
_start:
{
lean_object* v___x_5339_; lean_object* v_infoState_5340_; lean_object* v_trees_5341_; lean_object* v___x_5342_; lean_object* v_infoState_5343_; lean_object* v_env_5344_; lean_object* v_nextMacroScope_5345_; lean_object* v_ngen_5346_; lean_object* v_auxDeclNGen_5347_; lean_object* v_traceState_5348_; lean_object* v_cache_5349_; lean_object* v_recordedDeps_5350_; lean_object* v_messages_5351_; lean_object* v_snapshotTasks_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5373_; 
v___x_5339_ = lean_st_ref_get(v___y_5337_);
v_infoState_5340_ = lean_ctor_get(v___x_5339_, 8);
lean_inc_ref(v_infoState_5340_);
lean_dec(v___x_5339_);
v_trees_5341_ = lean_ctor_get(v_infoState_5340_, 2);
lean_inc_ref(v_trees_5341_);
lean_dec_ref(v_infoState_5340_);
v___x_5342_ = lean_st_ref_take(v___y_5337_);
v_infoState_5343_ = lean_ctor_get(v___x_5342_, 8);
v_env_5344_ = lean_ctor_get(v___x_5342_, 0);
v_nextMacroScope_5345_ = lean_ctor_get(v___x_5342_, 1);
v_ngen_5346_ = lean_ctor_get(v___x_5342_, 2);
v_auxDeclNGen_5347_ = lean_ctor_get(v___x_5342_, 3);
v_traceState_5348_ = lean_ctor_get(v___x_5342_, 4);
v_cache_5349_ = lean_ctor_get(v___x_5342_, 5);
v_recordedDeps_5350_ = lean_ctor_get(v___x_5342_, 6);
v_messages_5351_ = lean_ctor_get(v___x_5342_, 7);
v_snapshotTasks_5352_ = lean_ctor_get(v___x_5342_, 9);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5354_ = v___x_5342_;
v_isShared_5355_ = v_isSharedCheck_5373_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_snapshotTasks_5352_);
lean_inc(v_infoState_5343_);
lean_inc(v_messages_5351_);
lean_inc(v_recordedDeps_5350_);
lean_inc(v_cache_5349_);
lean_inc(v_traceState_5348_);
lean_inc(v_auxDeclNGen_5347_);
lean_inc(v_ngen_5346_);
lean_inc(v_nextMacroScope_5345_);
lean_inc(v_env_5344_);
lean_dec(v___x_5342_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5373_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
uint8_t v_enabled_5356_; lean_object* v_assignment_5357_; lean_object* v_lazyAssignment_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5371_; 
v_enabled_5356_ = lean_ctor_get_uint8(v_infoState_5343_, sizeof(void*)*3);
v_assignment_5357_ = lean_ctor_get(v_infoState_5343_, 0);
v_lazyAssignment_5358_ = lean_ctor_get(v_infoState_5343_, 1);
v_isSharedCheck_5371_ = !lean_is_exclusive(v_infoState_5343_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v_infoState_5343_, 2);
lean_dec(v_unused_5372_);
v___x_5360_ = v_infoState_5343_;
v_isShared_5361_ = v_isSharedCheck_5371_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_lazyAssignment_5358_);
lean_inc(v_assignment_5357_);
lean_dec(v_infoState_5343_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5371_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5362_; lean_object* v___x_5364_; 
v___x_5362_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1);
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 2, v___x_5362_);
v___x_5364_ = v___x_5360_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_assignment_5357_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v_lazyAssignment_5358_);
lean_ctor_set(v_reuseFailAlloc_5370_, 2, v___x_5362_);
lean_ctor_set_uint8(v_reuseFailAlloc_5370_, sizeof(void*)*3, v_enabled_5356_);
v___x_5364_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5366_; 
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 8, v___x_5364_);
v___x_5366_ = v___x_5354_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5369_; 
v_reuseFailAlloc_5369_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_env_5344_);
lean_ctor_set(v_reuseFailAlloc_5369_, 1, v_nextMacroScope_5345_);
lean_ctor_set(v_reuseFailAlloc_5369_, 2, v_ngen_5346_);
lean_ctor_set(v_reuseFailAlloc_5369_, 3, v_auxDeclNGen_5347_);
lean_ctor_set(v_reuseFailAlloc_5369_, 4, v_traceState_5348_);
lean_ctor_set(v_reuseFailAlloc_5369_, 5, v_cache_5349_);
lean_ctor_set(v_reuseFailAlloc_5369_, 6, v_recordedDeps_5350_);
lean_ctor_set(v_reuseFailAlloc_5369_, 7, v_messages_5351_);
lean_ctor_set(v_reuseFailAlloc_5369_, 8, v___x_5364_);
lean_ctor_set(v_reuseFailAlloc_5369_, 9, v_snapshotTasks_5352_);
v___x_5366_ = v_reuseFailAlloc_5369_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5367_ = lean_st_ref_put(v___y_5337_, v___x_5366_);
v___x_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5368_, 0, v_trees_5341_);
return v___x_5368_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5374_);
lean_dec(v___y_5374_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object* v___y_5377_, lean_object* v_mkInfoTree_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v_a_5386_, lean_object* v_a_x3f_5387_){
_start:
{
lean_object* v___x_5389_; lean_object* v_infoState_5390_; lean_object* v_trees_5391_; lean_object* v___x_5392_; 
v___x_5389_ = lean_st_ref_get(v___y_5377_);
v_infoState_5390_ = lean_ctor_get(v___x_5389_, 8);
lean_inc_ref(v_infoState_5390_);
lean_dec(v___x_5389_);
v_trees_5391_ = lean_ctor_get(v_infoState_5390_, 2);
lean_inc_ref(v_trees_5391_);
lean_dec_ref(v_infoState_5390_);
lean_inc(v___y_5377_);
lean_inc_ref(v___y_5385_);
lean_inc(v___y_5384_);
lean_inc_ref(v___y_5383_);
lean_inc(v___y_5382_);
lean_inc_ref(v___y_5381_);
lean_inc(v___y_5380_);
lean_inc_ref(v___y_5379_);
v___x_5392_ = lean_apply_10(v_mkInfoTree_5378_, v_trees_5391_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5377_, lean_box(0));
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5432_; 
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5395_ = v___x_5392_;
v_isShared_5396_ = v_isSharedCheck_5432_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5392_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5432_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5397_; lean_object* v_infoState_5398_; lean_object* v_env_5399_; lean_object* v_nextMacroScope_5400_; lean_object* v_ngen_5401_; lean_object* v_auxDeclNGen_5402_; lean_object* v_traceState_5403_; lean_object* v_cache_5404_; lean_object* v_recordedDeps_5405_; lean_object* v_messages_5406_; lean_object* v_snapshotTasks_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5431_; 
v___x_5397_ = lean_st_ref_take(v___y_5377_);
v_infoState_5398_ = lean_ctor_get(v___x_5397_, 8);
v_env_5399_ = lean_ctor_get(v___x_5397_, 0);
v_nextMacroScope_5400_ = lean_ctor_get(v___x_5397_, 1);
v_ngen_5401_ = lean_ctor_get(v___x_5397_, 2);
v_auxDeclNGen_5402_ = lean_ctor_get(v___x_5397_, 3);
v_traceState_5403_ = lean_ctor_get(v___x_5397_, 4);
v_cache_5404_ = lean_ctor_get(v___x_5397_, 5);
v_recordedDeps_5405_ = lean_ctor_get(v___x_5397_, 6);
v_messages_5406_ = lean_ctor_get(v___x_5397_, 7);
v_snapshotTasks_5407_ = lean_ctor_get(v___x_5397_, 9);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5409_ = v___x_5397_;
v_isShared_5410_ = v_isSharedCheck_5431_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_snapshotTasks_5407_);
lean_inc(v_infoState_5398_);
lean_inc(v_messages_5406_);
lean_inc(v_recordedDeps_5405_);
lean_inc(v_cache_5404_);
lean_inc(v_traceState_5403_);
lean_inc(v_auxDeclNGen_5402_);
lean_inc(v_ngen_5401_);
lean_inc(v_nextMacroScope_5400_);
lean_inc(v_env_5399_);
lean_dec(v___x_5397_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5431_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
uint8_t v_enabled_5411_; lean_object* v_assignment_5412_; lean_object* v_lazyAssignment_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5429_; 
v_enabled_5411_ = lean_ctor_get_uint8(v_infoState_5398_, sizeof(void*)*3);
v_assignment_5412_ = lean_ctor_get(v_infoState_5398_, 0);
v_lazyAssignment_5413_ = lean_ctor_get(v_infoState_5398_, 1);
v_isSharedCheck_5429_ = !lean_is_exclusive(v_infoState_5398_);
if (v_isSharedCheck_5429_ == 0)
{
lean_object* v_unused_5430_; 
v_unused_5430_ = lean_ctor_get(v_infoState_5398_, 2);
lean_dec(v_unused_5430_);
v___x_5415_ = v_infoState_5398_;
v_isShared_5416_ = v_isSharedCheck_5429_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_lazyAssignment_5413_);
lean_inc(v_assignment_5412_);
lean_dec(v_infoState_5398_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5429_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5420_; 
v___x_5417_ = lean_box(0);
v___x_5418_ = l_Lean_PersistentArray_push___redArg(v_a_5386_, v_a_5393_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 2, v___x_5418_);
v___x_5420_ = v___x_5415_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_assignment_5412_);
lean_ctor_set(v_reuseFailAlloc_5428_, 1, v_lazyAssignment_5413_);
lean_ctor_set(v_reuseFailAlloc_5428_, 2, v___x_5418_);
lean_ctor_set_uint8(v_reuseFailAlloc_5428_, sizeof(void*)*3, v_enabled_5411_);
v___x_5420_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
lean_object* v___x_5422_; 
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 8, v___x_5420_);
v___x_5422_ = v___x_5409_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_env_5399_);
lean_ctor_set(v_reuseFailAlloc_5427_, 1, v_nextMacroScope_5400_);
lean_ctor_set(v_reuseFailAlloc_5427_, 2, v_ngen_5401_);
lean_ctor_set(v_reuseFailAlloc_5427_, 3, v_auxDeclNGen_5402_);
lean_ctor_set(v_reuseFailAlloc_5427_, 4, v_traceState_5403_);
lean_ctor_set(v_reuseFailAlloc_5427_, 5, v_cache_5404_);
lean_ctor_set(v_reuseFailAlloc_5427_, 6, v_recordedDeps_5405_);
lean_ctor_set(v_reuseFailAlloc_5427_, 7, v_messages_5406_);
lean_ctor_set(v_reuseFailAlloc_5427_, 8, v___x_5420_);
lean_ctor_set(v_reuseFailAlloc_5427_, 9, v_snapshotTasks_5407_);
v___x_5422_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
lean_object* v___x_5423_; lean_object* v___x_5425_; 
v___x_5423_ = lean_st_ref_put(v___y_5377_, v___x_5422_);
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 0, v___x_5417_);
v___x_5425_ = v___x_5395_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5417_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5440_; 
lean_dec_ref(v_a_5386_);
v_a_5433_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5440_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5435_ = v___x_5392_;
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5392_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5438_; 
if (v_isShared_5436_ == 0)
{
v___x_5438_ = v___x_5435_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_a_5433_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object* v___y_5441_, lean_object* v_mkInfoTree_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v_a_5450_, lean_object* v_a_x3f_5451_, lean_object* v___y_5452_){
_start:
{
lean_object* v_res_5453_; 
v_res_5453_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5441_, v_mkInfoTree_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v_a_5450_, v_a_x3f_5451_);
lean_dec(v_a_x3f_5451_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v___y_5446_);
lean_dec_ref(v___y_5445_);
lean_dec(v___y_5444_);
lean_dec_ref(v___y_5443_);
lean_dec(v___y_5441_);
return v_res_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object* v_x_5454_, lean_object* v_mkInfoTree_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_){
_start:
{
lean_object* v___x_5465_; lean_object* v_infoState_5466_; uint8_t v_enabled_5467_; 
v___x_5465_ = lean_st_ref_get(v___y_5463_);
v_infoState_5466_ = lean_ctor_get(v___x_5465_, 8);
lean_inc_ref(v_infoState_5466_);
lean_dec(v___x_5465_);
v_enabled_5467_ = lean_ctor_get_uint8(v_infoState_5466_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5466_);
if (v_enabled_5467_ == 0)
{
lean_object* v___x_5468_; 
lean_dec_ref(v_mkInfoTree_5455_);
lean_inc(v___y_5463_);
lean_inc_ref(v___y_5462_);
lean_inc(v___y_5461_);
lean_inc_ref(v___y_5460_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
v___x_5468_ = lean_apply_9(v_x_5454_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, lean_box(0));
return v___x_5468_;
}
else
{
lean_object* v___x_5469_; lean_object* v_a_5470_; lean_object* v_r_5471_; 
v___x_5469_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5463_);
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
lean_inc(v_a_5470_);
lean_dec_ref(v___x_5469_);
lean_inc(v___y_5463_);
lean_inc_ref(v___y_5462_);
lean_inc(v___y_5461_);
lean_inc_ref(v___y_5460_);
lean_inc(v___y_5459_);
lean_inc_ref(v___y_5458_);
lean_inc(v___y_5457_);
lean_inc_ref(v___y_5456_);
v_r_5471_ = lean_apply_9(v_x_5454_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, lean_box(0));
if (lean_obj_tag(v_r_5471_) == 0)
{
lean_object* v_a_5472_; lean_object* v___x_5474_; uint8_t v_isShared_5475_; uint8_t v_isSharedCheck_5496_; 
v_a_5472_ = lean_ctor_get(v_r_5471_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v_r_5471_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5474_ = v_r_5471_;
v_isShared_5475_ = v_isSharedCheck_5496_;
goto v_resetjp_5473_;
}
else
{
lean_inc(v_a_5472_);
lean_dec(v_r_5471_);
v___x_5474_ = lean_box(0);
v_isShared_5475_ = v_isSharedCheck_5496_;
goto v_resetjp_5473_;
}
v_resetjp_5473_:
{
lean_object* v___x_5477_; 
lean_inc(v_a_5472_);
if (v_isShared_5475_ == 0)
{
lean_ctor_set_tag(v___x_5474_, 1);
v___x_5477_ = v___x_5474_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v_a_5472_);
v___x_5477_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5478_; 
v___x_5478_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5463_, v_mkInfoTree_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v_a_5470_, v___x_5477_);
lean_dec_ref(v___x_5477_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5485_; 
v_isSharedCheck_5485_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5485_ == 0)
{
lean_object* v_unused_5486_; 
v_unused_5486_ = lean_ctor_get(v___x_5478_, 0);
lean_dec(v_unused_5486_);
v___x_5480_ = v___x_5478_;
v_isShared_5481_ = v_isSharedCheck_5485_;
goto v_resetjp_5479_;
}
else
{
lean_dec(v___x_5478_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5485_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v___x_5483_; 
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v_a_5472_);
v___x_5483_ = v___x_5480_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v_a_5472_);
v___x_5483_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
return v___x_5483_;
}
}
}
else
{
lean_object* v_a_5487_; lean_object* v___x_5489_; uint8_t v_isShared_5490_; uint8_t v_isSharedCheck_5494_; 
lean_dec(v_a_5472_);
v_a_5487_ = lean_ctor_get(v___x_5478_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5494_ == 0)
{
v___x_5489_ = v___x_5478_;
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
else
{
lean_inc(v_a_5487_);
lean_dec(v___x_5478_);
v___x_5489_ = lean_box(0);
v_isShared_5490_ = v_isSharedCheck_5494_;
goto v_resetjp_5488_;
}
v_resetjp_5488_:
{
lean_object* v___x_5492_; 
if (v_isShared_5490_ == 0)
{
v___x_5492_ = v___x_5489_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
}
}
}
else
{
lean_object* v_a_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; 
v_a_5497_ = lean_ctor_get(v_r_5471_, 0);
lean_inc(v_a_5497_);
lean_dec_ref_known(v_r_5471_, 1);
v___x_5498_ = lean_box(0);
v___x_5499_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5463_, v_mkInfoTree_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v_a_5470_, v___x_5498_);
if (lean_obj_tag(v___x_5499_) == 0)
{
lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5499_);
if (v_isSharedCheck_5506_ == 0)
{
lean_object* v_unused_5507_; 
v_unused_5507_ = lean_ctor_get(v___x_5499_, 0);
lean_dec(v_unused_5507_);
v___x_5501_ = v___x_5499_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_dec(v___x_5499_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
lean_ctor_set_tag(v___x_5501_, 1);
lean_ctor_set(v___x_5501_, 0, v_a_5497_);
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5497_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
else
{
lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5515_; 
lean_dec(v_a_5497_);
v_a_5508_ = lean_ctor_get(v___x_5499_, 0);
v_isSharedCheck_5515_ = !lean_is_exclusive(v___x_5499_);
if (v_isSharedCheck_5515_ == 0)
{
v___x_5510_ = v___x_5499_;
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5499_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5515_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v___x_5513_; 
if (v_isShared_5511_ == 0)
{
v___x_5513_ = v___x_5510_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_a_5508_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object* v_x_5516_, lean_object* v_mkInfoTree_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5516_, v_mkInfoTree_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
lean_dec(v___y_5525_);
lean_dec_ref(v___y_5524_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v___y_5519_);
lean_dec_ref(v___y_5518_);
return v_res_5527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object* v_upperBound_5538_, lean_object* v_enterArgsAndSeps_5539_, lean_object* v_a_5540_, lean_object* v_b_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_){
_start:
{
uint8_t v___x_5551_; 
v___x_5551_ = lean_nat_dec_lt(v_a_5540_, v_upperBound_5538_);
if (v___x_5551_ == 0)
{
lean_object* v___x_5552_; 
lean_dec(v_a_5540_);
v___x_5552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5552_, 0, v_b_5541_);
return v___x_5552_;
}
else
{
lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___y_5561_; lean_object* v___x_5590_; lean_object* v___x_5591_; uint8_t v___x_5592_; 
v___x_5553_ = lean_unsigned_to_nat(2u);
v___x_5554_ = lean_box(0);
v___x_5555_ = lean_box(0);
v___x_5556_ = lean_unsigned_to_nat(0u);
v___x_5557_ = lean_unsigned_to_nat(1u);
v___x_5558_ = lean_nat_mul(v___x_5553_, v_a_5540_);
v___x_5559_ = lean_array_get_borrowed(v___x_5554_, v_enterArgsAndSeps_5539_, v___x_5558_);
v___x_5590_ = lean_nat_add(v___x_5558_, v___x_5557_);
lean_dec(v___x_5558_);
v___x_5591_ = lean_array_get_size(v_enterArgsAndSeps_5539_);
v___x_5592_ = lean_nat_dec_lt(v___x_5590_, v___x_5591_);
if (v___x_5592_ == 0)
{
lean_dec(v___x_5590_);
v___y_5561_ = v___x_5554_;
goto v___jp_5560_;
}
else
{
lean_object* v___x_5593_; 
v___x_5593_ = lean_array_fget_borrowed(v_enterArgsAndSeps_5539_, v___x_5590_);
lean_dec(v___x_5590_);
lean_inc(v___x_5593_);
v___y_5561_ = v___x_5593_;
goto v___jp_5560_;
}
v___jp_5560_:
{
lean_object* v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; uint8_t v___x_5573_; lean_object* v___x_5574_; lean_object* v___f_5575_; lean_object* v___x_5576_; 
v___x_5562_ = lean_mk_empty_array_with_capacity(v___x_5553_);
lean_inc_n(v___x_5559_, 3);
v___x_5563_ = lean_array_push(v___x_5562_, v___x_5559_);
v___x_5564_ = lean_array_push(v___x_5563_, v___y_5561_);
v___x_5565_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5566_ = lean_box(2);
v___x_5567_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5566_);
lean_ctor_set(v___x_5567_, 1, v___x_5565_);
lean_ctor_set(v___x_5567_, 2, v___x_5564_);
v___x_5568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0));
v___x_5569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1));
v___x_5570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2));
v___x_5571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3));
v___x_5572_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3));
v___x_5573_ = l_Lean_Syntax_isOfKind(v___x_5559_, v___x_5572_);
v___x_5574_ = lean_box(v___x_5573_);
v___f_5575_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_5575_, 0, v___x_5574_);
lean_closure_set(v___f_5575_, 1, v___x_5555_);
lean_closure_set(v___f_5575_, 2, v___x_5559_);
lean_closure_set(v___f_5575_, 3, v___x_5556_);
lean_closure_set(v___f_5575_, 4, v___x_5568_);
lean_closure_set(v___f_5575_, 5, v___x_5569_);
lean_closure_set(v___f_5575_, 6, v___x_5570_);
lean_closure_set(v___f_5575_, 7, v___x_5571_);
lean_closure_set(v___f_5575_, 8, v___x_5565_);
v___x_5576_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5567_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
if (lean_obj_tag(v___x_5576_) == 0)
{
lean_object* v_a_5577_; lean_object* v___f_5578_; lean_object* v___x_5579_; 
v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
lean_inc(v_a_5577_);
lean_dec_ref_known(v___x_5576_, 1);
v___f_5578_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5578_, 0, v_a_5577_);
v___x_5579_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5575_, v___f_5578_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v___x_5580_; 
lean_dec_ref_known(v___x_5579_, 1);
v___x_5580_ = lean_nat_add(v_a_5540_, v___x_5557_);
lean_dec(v_a_5540_);
v_a_5540_ = v___x_5580_;
v_b_5541_ = v___x_5555_;
goto _start;
}
else
{
lean_dec(v_a_5540_);
return v___x_5579_;
}
}
else
{
lean_object* v_a_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5589_; 
lean_dec_ref(v___f_5575_);
lean_dec(v_a_5540_);
v_a_5582_ = lean_ctor_get(v___x_5576_, 0);
v_isSharedCheck_5589_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5589_ == 0)
{
v___x_5584_ = v___x_5576_;
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_a_5582_);
lean_dec(v___x_5576_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5589_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5587_; 
if (v_isShared_5585_ == 0)
{
v___x_5587_ = v___x_5584_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_a_5582_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object* v_upperBound_5594_, lean_object* v_enterArgsAndSeps_5595_, lean_object* v_a_5596_, lean_object* v_b_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_){
_start:
{
lean_object* v_res_5607_; 
v_res_5607_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5594_, v_enterArgsAndSeps_5595_, v_a_5596_, v_b_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
lean_dec(v___y_5605_);
lean_dec_ref(v___y_5604_);
lean_dec(v___y_5603_);
lean_dec_ref(v___y_5602_);
lean_dec(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec(v___y_5599_);
lean_dec_ref(v___y_5598_);
lean_dec_ref(v_enterArgsAndSeps_5595_);
lean_dec(v_upperBound_5594_);
return v_res_5607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object* v_stx_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_){
_start:
{
lean_object* v___x_5620_; lean_object* v_token_5621_; lean_object* v___x_5622_; lean_object* v_lbrak_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v_enterArgsAndSeps_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___f_5634_; lean_object* v___x_5635_; 
v___x_5620_ = lean_unsigned_to_nat(0u);
v_token_5621_ = l_Lean_Syntax_getArg(v_stx_5610_, v___x_5620_);
v___x_5622_ = lean_unsigned_to_nat(1u);
v_lbrak_5623_ = l_Lean_Syntax_getArg(v_stx_5610_, v___x_5622_);
v___x_5624_ = lean_unsigned_to_nat(2u);
v___x_5625_ = l_Lean_Syntax_getArg(v_stx_5610_, v___x_5624_);
v_enterArgsAndSeps_5626_ = l_Lean_Syntax_getArgs(v___x_5625_);
lean_dec(v___x_5625_);
v___x_5627_ = lean_mk_empty_array_with_capacity(v___x_5624_);
v___x_5628_ = lean_array_push(v___x_5627_, v_token_5621_);
v___x_5629_ = lean_array_push(v___x_5628_, v_lbrak_5623_);
v___x_5630_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5631_ = lean_box(2);
v___x_5632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5632_, 0, v___x_5631_);
lean_ctor_set(v___x_5632_, 1, v___x_5630_);
lean_ctor_set(v___x_5632_, 2, v___x_5629_);
v___x_5633_ = lean_box(0);
v___f_5634_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalEnter___closed__0));
v___x_5635_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5632_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_);
if (lean_obj_tag(v___x_5635_) == 0)
{
lean_object* v_a_5636_; lean_object* v___f_5637_; lean_object* v___x_5638_; 
v_a_5636_ = lean_ctor_get(v___x_5635_, 0);
lean_inc(v_a_5636_);
lean_dec_ref_known(v___x_5635_, 1);
v___f_5637_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5637_, 0, v_a_5636_);
v___x_5638_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5634_, v___f_5637_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_);
if (lean_obj_tag(v___x_5638_) == 0)
{
lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
lean_dec_ref_known(v___x_5638_, 1);
v___x_5639_ = lean_array_get_size(v_enterArgsAndSeps_5626_);
v___x_5640_ = lean_nat_add(v___x_5639_, v___x_5622_);
v___x_5641_ = lean_nat_shiftr(v___x_5640_, v___x_5622_);
lean_dec(v___x_5640_);
v___x_5642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v___x_5641_, v_enterArgsAndSeps_5626_, v___x_5620_, v___x_5633_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_, v_a_5617_, v_a_5618_);
lean_dec_ref(v_enterArgsAndSeps_5626_);
lean_dec(v___x_5641_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5649_; 
v_isSharedCheck_5649_ = !lean_is_exclusive(v___x_5642_);
if (v_isSharedCheck_5649_ == 0)
{
lean_object* v_unused_5650_; 
v_unused_5650_ = lean_ctor_get(v___x_5642_, 0);
lean_dec(v_unused_5650_);
v___x_5644_ = v___x_5642_;
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
else
{
lean_dec(v___x_5642_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5649_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v___x_5647_; 
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 0, v___x_5633_);
v___x_5647_ = v___x_5644_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5648_; 
v_reuseFailAlloc_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5648_, 0, v___x_5633_);
v___x_5647_ = v_reuseFailAlloc_5648_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
return v___x_5647_;
}
}
}
else
{
return v___x_5642_;
}
}
else
{
lean_dec_ref(v_enterArgsAndSeps_5626_);
return v___x_5638_;
}
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
lean_dec_ref(v_enterArgsAndSeps_5626_);
v_a_5651_ = lean_ctor_get(v___x_5635_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5635_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5635_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5635_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object* v_stx_5659_, lean_object* v_a_5660_, lean_object* v_a_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_){
_start:
{
lean_object* v_res_5669_; 
v_res_5669_ = l_Lean_Elab_Tactic_Conv_evalEnter(v_stx_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_);
lean_dec(v_a_5667_);
lean_dec_ref(v_a_5666_);
lean_dec(v_a_5665_);
lean_dec_ref(v_a_5664_);
lean_dec(v_a_5663_);
lean_dec_ref(v_a_5662_);
lean_dec(v_a_5661_);
lean_dec_ref(v_a_5660_);
lean_dec(v_stx_5659_);
return v_res_5669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
lean_object* v___x_5679_; 
v___x_5679_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5677_);
return v___x_5679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_){
_start:
{
lean_object* v_res_5689_; 
v_res_5689_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
lean_dec(v___y_5687_);
lean_dec_ref(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
return v_res_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object* v_00_u03b1_5690_, lean_object* v_x_5691_, lean_object* v_mkInfoTree_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_){
_start:
{
lean_object* v___x_5702_; 
v___x_5702_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5691_, v_mkInfoTree_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_);
return v___x_5702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object* v_00_u03b1_5703_, lean_object* v_x_5704_, lean_object* v_mkInfoTree_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_){
_start:
{
lean_object* v_res_5715_; 
v_res_5715_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(v_00_u03b1_5703_, v_x_5704_, v_mkInfoTree_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_);
lean_dec(v___y_5713_);
lean_dec_ref(v___y_5712_);
lean_dec(v___y_5711_);
lean_dec_ref(v___y_5710_);
lean_dec(v___y_5709_);
lean_dec_ref(v___y_5708_);
lean_dec(v___y_5707_);
lean_dec_ref(v___y_5706_);
return v_res_5715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object* v_upperBound_5716_, lean_object* v_enterArgsAndSeps_5717_, lean_object* v_inst_5718_, lean_object* v_R_5719_, lean_object* v_a_5720_, lean_object* v_b_5721_, lean_object* v_c_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_){
_start:
{
lean_object* v___x_5732_; 
v___x_5732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5716_, v_enterArgsAndSeps_5717_, v_a_5720_, v_b_5721_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_);
return v___x_5732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object* v_upperBound_5733_, lean_object* v_enterArgsAndSeps_5734_, lean_object* v_inst_5735_, lean_object* v_R_5736_, lean_object* v_a_5737_, lean_object* v_b_5738_, lean_object* v_c_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
lean_object* v_res_5749_; 
v_res_5749_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(v_upperBound_5733_, v_enterArgsAndSeps_5734_, v_inst_5735_, v_R_5736_, v_a_5737_, v_b_5738_, v_c_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
lean_dec(v___y_5747_);
lean_dec_ref(v___y_5746_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5743_);
lean_dec_ref(v___y_5742_);
lean_dec(v___y_5741_);
lean_dec_ref(v___y_5740_);
lean_dec_ref(v_enterArgsAndSeps_5734_);
lean_dec(v_upperBound_5733_);
return v_res_5749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1(){
_start:
{
lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; 
v___x_5765_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1));
v___x_5767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3));
v___x_5768_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___boxed), 10, 0);
v___x_5769_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5765_, v___x_5766_, v___x_5767_, v___x_5768_);
return v___x_5769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object* v_a_5770_){
_start:
{
lean_object* v_res_5771_; 
v_res_5771_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
return v_res_5771_;
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
