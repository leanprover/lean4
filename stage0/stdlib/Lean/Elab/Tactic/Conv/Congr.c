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
lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSkip___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4_;
v_res_4_ = l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___redArg___boxed(lean_object* v_a_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
return v_res_6_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalSkip(lean_object* v_x_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_Tactic_Conv_evalSkip___redArg();
return v___x_17_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalSkip_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_7_ = stack[0].m_obj;
lean_object* v_a_8_ = stack[1].m_obj;
lean_object* v_a_9_ = stack[2].m_obj;
lean_object* v_a_10_ = stack[3].m_obj;
lean_object* v_a_11_ = stack[4].m_obj;
lean_object* v_a_12_ = stack[5].m_obj;
lean_object* v_a_13_ = stack[6].m_obj;
lean_object* v_a_14_ = stack[7].m_obj;
lean_object* v_a_15_ = stack[8].m_obj;
lean_object* v_res_18_;
v_res_18_ = l_Lean_Elab_Tactic_Conv_evalSkip(v_x_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalSkip___boxed(lean_object* v_x_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Elab_Tactic_Conv_evalSkip(v_x_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
lean_dec(v_a_27_);
lean_dec_ref(v_a_26_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_x_19_);
return v_res_29_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_50_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__5));
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8));
v___x_53_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalSkip___boxed), 10, 0);
v___x_54_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_50_, v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_55_;
v_res_55_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
stack->m_obj
 = v_res_55_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___boxed(lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1();
return v_res_57_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3(){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__8));
v___x_85_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___closed__6));
v___x_86_ = l_Lean_addBuiltinDeclarationRanges(v___x_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3___boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip_declRange__3();
return v_res_89_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(lean_object* v_msgData_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_env_97_; uint8_t v___x_98_; lean_object* v_env_99_; lean_object* v___x_100_; lean_object* v_toCold_101_; lean_object* v_mctx_102_; lean_object* v_lctx_103_; lean_object* v_options_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_96_ = lean_st_ref_get(v___y_94_);
v_env_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_env_97_);
lean_dec(v___x_96_);
v___x_98_ = 0;
v_env_99_ = l_Lean_Environment_setRecordingDeps(v_env_97_, v___x_98_);
v___x_100_ = lean_st_ref_get(v___y_92_);
v_toCold_101_ = lean_ctor_get(v___y_93_, 0);
v_mctx_102_ = lean_ctor_get(v___x_100_, 0);
lean_inc_ref(v_mctx_102_);
lean_dec(v___x_100_);
v_lctx_103_ = lean_ctor_get(v___y_91_, 2);
v_options_104_ = lean_ctor_get(v_toCold_101_, 2);
lean_inc_ref(v_options_104_);
lean_inc_ref(v_lctx_103_);
v___x_105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_105_, 0, v_env_99_);
lean_ctor_set(v___x_105_, 1, v_mctx_102_);
lean_ctor_set(v___x_105_, 2, v_lctx_103_);
lean_ctor_set(v___x_105_, 3, v_options_104_);
v___x_106_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_msgData_90_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_90_ = stack[0].m_obj;
lean_object* v___y_91_ = stack[1].m_obj;
lean_object* v___y_92_ = stack[2].m_obj;
lean_object* v___y_93_ = stack[3].m_obj;
lean_object* v___y_94_ = stack[4].m_obj;
lean_object* v_res_108_;
v_res_108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msgData_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0___boxed(lean_object* v_msgData_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msgData_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_115_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_ref_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
v_ref_122_ = lean_ctor_get(v___y_119_, 2);
v___x_123_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_132_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_inc(v_ref_122_);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_ref_122_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 1);
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_116_ = stack[0].m_obj;
lean_object* v___y_117_ = stack[1].m_obj;
lean_object* v___y_118_ = stack[2].m_obj;
lean_object* v___y_119_ = stack[3].m_obj;
lean_object* v___y_120_ = stack[4].m_obj;
lean_object* v_res_133_;
v_res_133_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg___boxed(lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_140_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__0));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(lean_object* v_mvarId_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___y_158_; lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3));
v___x_165_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_164_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
v___x_167_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4));
v___x_168_ = lean_box(0);
v___x_169_ = l_Lean_MVarId_apply(v_mvarId_151_, v_a_166_, v___x_167_, v___x_168_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_169_, 1);
if (lean_obj_tag(v_a_170_) == 1)
{
lean_object* v_tail_171_; 
v_tail_171_ = lean_ctor_get(v_a_170_, 1);
lean_inc(v_tail_171_);
if (lean_obj_tag(v_tail_171_) == 1)
{
lean_object* v_tail_172_; 
v_tail_172_ = lean_ctor_get(v_tail_171_, 1);
lean_inc(v_tail_172_);
if (lean_obj_tag(v_tail_172_) == 1)
{
lean_object* v_tail_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_218_; 
v_tail_173_ = lean_ctor_get(v_tail_172_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_tail_172_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_tail_172_, 0);
lean_dec(v_unused_219_);
v___x_175_ = v_tail_172_;
v_isShared_176_ = v_isSharedCheck_218_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_tail_173_);
lean_dec(v_tail_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_218_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
if (lean_obj_tag(v_tail_173_) == 1)
{
lean_object* v_tail_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_216_; 
v_tail_177_ = lean_ctor_get(v_tail_173_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_tail_173_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; 
v_unused_217_ = lean_ctor_get(v_tail_173_, 0);
lean_dec(v_unused_217_);
v___x_179_ = v_tail_173_;
v_isShared_180_ = v_isSharedCheck_216_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_tail_177_);
lean_dec(v_tail_173_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_216_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
if (lean_obj_tag(v_tail_177_) == 0)
{
lean_object* v_head_181_; lean_object* v_head_182_; lean_object* v___x_183_; 
v_head_181_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_head_181_);
lean_dec_ref_known(v_a_170_, 2);
v_head_182_ = lean_ctor_get(v_tail_171_, 0);
lean_inc(v_head_182_);
lean_dec_ref_known(v_tail_171_, 2);
v___x_183_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_181_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v___x_185_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_head_182_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_199_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_199_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_199_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v_a_186_);
v___x_191_ = v___x_179_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_186_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_tail_177_);
v___x_191_ = v_reuseFailAlloc_198_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_193_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_191_);
lean_ctor_set(v___x_175_, 0, v_a_184_);
v___x_193_ = v___x_175_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_184_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_193_);
v___x_195_ = v___x_188_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_a_184_);
lean_del_object(v___x_179_);
lean_del_object(v___x_175_);
v_a_200_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_185_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_185_);
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
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec(v_head_182_);
lean_del_object(v___x_179_);
lean_del_object(v___x_175_);
v_a_208_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_183_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_183_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_del_object(v___x_179_);
lean_dec(v_tail_177_);
lean_del_object(v___x_175_);
lean_dec_ref_known(v_tail_171_, 2);
lean_dec_ref_known(v_a_170_, 2);
v___y_158_ = v_a_152_;
v___y_159_ = v_a_153_;
v___y_160_ = v_a_154_;
v___y_161_ = v_a_155_;
goto v___jp_157_;
}
}
}
else
{
lean_del_object(v___x_175_);
lean_dec(v_tail_173_);
lean_dec_ref_known(v_tail_171_, 2);
lean_dec_ref_known(v_a_170_, 2);
v___y_158_ = v_a_152_;
v___y_159_ = v_a_153_;
v___y_160_ = v_a_154_;
v___y_161_ = v_a_155_;
goto v___jp_157_;
}
}
}
else
{
lean_dec(v_tail_172_);
lean_dec_ref_known(v_tail_171_, 2);
lean_dec_ref_known(v_a_170_, 2);
v___y_158_ = v_a_152_;
v___y_159_ = v_a_153_;
v___y_160_ = v_a_154_;
v___y_161_ = v_a_155_;
goto v___jp_157_;
}
}
else
{
lean_dec_ref_known(v_a_170_, 2);
lean_dec(v_tail_171_);
v___y_158_ = v_a_152_;
v___y_159_ = v_a_153_;
v___y_160_ = v_a_154_;
v___y_161_ = v_a_155_;
goto v___jp_157_;
}
}
else
{
lean_dec(v_a_170_);
v___y_158_ = v_a_152_;
v___y_159_ = v_a_153_;
v___y_160_ = v_a_154_;
v___y_161_ = v_a_155_;
goto v___jp_157_;
}
}
else
{
return v___x_169_;
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_mvarId_151_);
v_a_220_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_165_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_165_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
v___jp_157_:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__1);
v___x_163_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_162_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
return v___x_163_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_151_ = stack[0].m_obj;
lean_object* v_a_152_ = stack[1].m_obj;
lean_object* v_a_153_ = stack[2].m_obj;
lean_object* v_a_154_ = stack[3].m_obj;
lean_object* v_a_155_ = stack[4].m_obj;
lean_object* v_res_228_;
v_res_228_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___boxed(lean_object* v_mvarId_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
return v_res_235_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_object* v_00_u03b1_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
return v___x_243_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_237_ = stack[1].m_obj;
lean_object* v___y_238_ = stack[2].m_obj;
lean_object* v___y_239_ = stack[3].m_obj;
lean_object* v___y_240_ = stack[4].m_obj;
lean_object* v___y_241_ = stack[5].m_obj;
lean_object* v_res_244_;
v_res_244_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(lean_box(0), v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___boxed(lean_object* v_00_u03b1_245_, lean_object* v_msg_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0(v_00_u03b1_245_, v_msg_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_252_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(lean_object* v_e_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_Lean_Expr_isArrow(v_e_253_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_box(v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = l_Lean_Expr_bindingDomain_x21(v_e_253_);
v___x_263_ = l_Lean_Meta_isProp(v___x_262_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; uint8_t v___x_265_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v___x_265_ = lean_unbox(v_a_264_);
if (v___x_265_ == 0)
{
return v___x_263_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec_ref_known(v___x_263_, 1);
v___x_266_ = l_Lean_Expr_bindingBody_x21(v_e_253_);
v___x_267_ = l_Lean_Meta_isProp(v___x_266_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
return v___x_267_;
}
}
else
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_253_ = stack[0].m_obj;
lean_object* v_a_254_ = stack[1].m_obj;
lean_object* v_a_255_ = stack[2].m_obj;
lean_object* v_a_256_ = stack[3].m_obj;
lean_object* v_a_257_ = stack[4].m_obj;
lean_object* v_res_268_;
v_res_268_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v_e_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies___boxed(lean_object* v_e_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v_e_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec_ref(v_e_269_);
return v_res_275_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(lean_object* v_msg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___f_283_; lean_object* v___x_8175__overap_284_; lean_object* v___x_285_; 
v___f_283_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_8175__overap_284_ = lean_panic_fn_borrowed(v___f_283_, v_msg_277_);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
v___x_285_ = lean_apply_5(v___x_8175__overap_284_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, lean_box(0));
return v___x_285_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_277_ = stack[0].m_obj;
lean_object* v___y_278_ = stack[1].m_obj;
lean_object* v___y_279_ = stack[2].m_obj;
lean_object* v___y_280_ = stack[3].m_obj;
lean_object* v___y_281_ = stack[4].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___boxed(lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_293_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(lean_object* v___x_294_, lean_object* v_fst_295_, lean_object* v_fst_296_, lean_object* v_fst_297_, lean_object* v_snd_298_, lean_object* v_tag_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; 
lean_inc_ref(v___x_294_);
v___x_305_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_294_, v_tag_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_330_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_330_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_fst_310_; lean_object* v_snd_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_329_; 
v_fst_310_ = lean_ctor_get(v_a_306_, 0);
v_snd_311_ = lean_ctor_get(v_a_306_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_a_306_);
if (v_isSharedCheck_329_ == 0)
{
v___x_313_ = v_a_306_;
v_isShared_314_ = v_isSharedCheck_329_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snd_311_);
lean_inc(v_fst_310_);
lean_dec(v_a_306_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_329_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
lean_inc(v_fst_310_);
v___x_315_ = l_Lean_Expr_app___override(v_fst_295_, v_fst_310_);
lean_inc(v_snd_311_);
v___x_316_ = l_Lean_mkApp3(v_fst_296_, v___x_294_, v_fst_310_, v_snd_311_);
v___x_317_ = l_Lean_Expr_mvarId_x21(v_snd_311_);
lean_dec(v_snd_311_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___x_319_ = lean_array_push(v_fst_297_, v___x_318_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_snd_298_);
lean_ctor_set(v___x_313_, 0, v___x_319_);
v___x_321_ = v___x_313_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_snd_298_);
v___x_321_ = v_reuseFailAlloc_328_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_316_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_315_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_324_);
v___x_326_ = v___x_308_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
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
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_snd_298_);
lean_dec(v_fst_297_);
lean_dec(v_fst_296_);
lean_dec(v_fst_295_);
lean_dec_ref(v___x_294_);
v_a_331_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_305_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_305_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_294_ = stack[0].m_obj;
lean_object* v_fst_295_ = stack[1].m_obj;
lean_object* v_fst_296_ = stack[2].m_obj;
lean_object* v_fst_297_ = stack[3].m_obj;
lean_object* v_snd_298_ = stack[4].m_obj;
lean_object* v_tag_299_ = stack[5].m_obj;
lean_object* v___y_300_ = stack[6].m_obj;
lean_object* v___y_301_ = stack[7].m_obj;
lean_object* v___y_302_ = stack[8].m_obj;
lean_object* v___y_303_ = stack[9].m_obj;
lean_object* v_res_339_;
v_res_339_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_294_, v_fst_295_, v_fst_296_, v_fst_297_, v_snd_298_, v_tag_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1___boxed(lean_object* v___x_340_, lean_object* v_fst_341_, lean_object* v_fst_342_, lean_object* v_fst_343_, lean_object* v_snd_344_, lean_object* v_tag_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_340_, v_fst_341_, v_fst_342_, v_fst_343_, v_snd_344_, v_tag_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
return v_res_351_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_355_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_356_ = lean_unsigned_to_nat(30u);
v___x_357_ = lean_unsigned_to_nat(68u);
v___x_358_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__1));
v___x_359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_360_ = l_mkPanicMessageWithDecl(v___x_359_, v___x_358_, v___x_357_, v___x_356_, v___x_355_);
return v___x_360_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(lean_object* v_fst_361_, lean_object* v_snd_362_, lean_object* v_fst_363_, lean_object* v_fst_364_, lean_object* v_00___365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__3);
v___x_372_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_371_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_383_; 
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v___x_372_, 0);
lean_dec(v_unused_384_);
v___x_374_ = v___x_372_;
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
else
{
lean_dec(v___x_372_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_383_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_fst_361_);
lean_ctor_set(v___x_376_, 1, v_snd_362_);
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v_fst_363_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_378_, 0, v_fst_364_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_379_);
v___x_381_ = v___x_374_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_fst_364_);
lean_dec(v_fst_363_);
lean_dec(v_snd_362_);
lean_dec(v_fst_361_);
v_a_385_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_372_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_372_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_361_ = stack[0].m_obj;
lean_object* v_snd_362_ = stack[1].m_obj;
lean_object* v_fst_363_ = stack[2].m_obj;
lean_object* v_fst_364_ = stack[3].m_obj;
lean_object* v_00___365_ = stack[4].m_obj;
lean_object* v___y_366_ = stack[5].m_obj;
lean_object* v___y_367_ = stack[6].m_obj;
lean_object* v___y_368_ = stack[7].m_obj;
lean_object* v___y_369_ = stack[8].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_361_, v_snd_362_, v_fst_363_, v_fst_364_, v_00___365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___boxed(lean_object* v_fst_394_, lean_object* v_snd_395_, lean_object* v_fst_396_, lean_object* v_fst_397_, lean_object* v_00___398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_394_, v_snd_395_, v_fst_396_, v_fst_397_, v_00___398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_404_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(lean_object* v_upperBound_405_, lean_object* v_args_406_, uint8_t v_nameSubgoals_407_, lean_object* v_origTag_408_, lean_object* v_a_409_, lean_object* v___x_410_, uint8_t v_addImplicitArgs_411_, lean_object* v_a_412_, lean_object* v_b_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_a_420_; lean_object* v___y_425_; uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_lt(v_a_412_, v_upperBound_405_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_b_413_);
return v___x_445_;
}
else
{
lean_object* v_snd_446_; lean_object* v_snd_447_; lean_object* v_fst_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_589_; 
v_snd_446_ = lean_ctor_get(v_b_413_, 1);
lean_inc(v_snd_446_);
v_snd_447_ = lean_ctor_get(v_snd_446_, 1);
lean_inc(v_snd_447_);
v_fst_448_ = lean_ctor_get(v_b_413_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_b_413_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v_b_413_, 1);
lean_dec(v_unused_590_);
v___x_450_ = v_b_413_;
v_isShared_451_ = v_isSharedCheck_589_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_fst_448_);
lean_dec(v_b_413_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_589_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_fst_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_587_; 
v_fst_452_ = lean_ctor_get(v_snd_446_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_snd_446_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_snd_446_, 1);
lean_dec(v_unused_588_);
v___x_454_ = v_snd_446_;
v_isShared_455_ = v_isSharedCheck_587_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_fst_452_);
lean_dec(v_snd_446_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_587_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_fst_456_; lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_586_; 
v_fst_456_ = lean_ctor_get(v_snd_447_, 0);
v_snd_457_ = lean_ctor_get(v_snd_447_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_snd_447_);
if (v_isSharedCheck_586_ == 0)
{
v___x_459_ = v_snd_447_;
v_isShared_460_ = v_isSharedCheck_586_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_inc(v_fst_456_);
lean_dec(v_snd_447_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_586_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_paramInfo_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_paramInfo_461_ = lean_ctor_get(v_a_409_, 0);
v___x_462_ = l_Lean_instInhabitedExpr;
v___x_463_ = l_Lean_Meta_instInhabitedParamInfo_default;
v___x_464_ = lean_array_get_borrowed(v___x_462_, v_args_406_, v_a_412_);
v___x_465_ = lean_array_get_borrowed(v___x_463_, v_paramInfo_461_, v_a_412_);
v___x_466_ = lean_array_fget_borrowed(v___x_410_, v_a_412_);
v___x_467_ = lean_unbox(v___x_466_);
switch(v___x_467_)
{
case 1:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_del_object(v___x_459_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
v___x_468_ = lean_box(0);
v___x_469_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_456_, v_snd_457_, v_fst_452_, v_fst_448_, v___x_468_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_425_ = v___x_469_;
goto v___jp_424_;
}
case 2:
{
if (v_addImplicitArgs_411_ == 0)
{
uint8_t v___x_495_; 
v___x_495_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_465_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_inc_n(v___x_464_, 2);
v___x_496_ = l_Lean_Expr_app___override(v_fst_448_, v___x_464_);
v___x_497_ = l_Lean_Meta_mkEqRefl(v___x_464_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
lean_inc_n(v___x_464_, 2);
v___x_499_ = l_Lean_mkApp3(v_fst_452_, v___x_464_, v___x_464_, v_a_498_);
if (v_isShared_460_ == 0)
{
v___x_501_ = v___x_459_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_fst_456_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_snd_457_);
v___x_501_ = v_reuseFailAlloc_508_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_501_);
lean_ctor_set(v___x_454_, 0, v___x_499_);
v___x_503_ = v___x_454_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_503_);
lean_ctor_set(v___x_450_, 0, v___x_496_);
v___x_505_ = v___x_450_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
v_a_420_ = v___x_505_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v___x_496_);
lean_del_object(v___x_459_);
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_del_object(v___x_454_);
lean_dec(v_fst_452_);
lean_del_object(v___x_450_);
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_509_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_497_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_497_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_del_object(v___x_459_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_470_;
}
}
else
{
lean_del_object(v___x_459_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
goto v___jp_470_;
}
v___jp_470_:
{
if (v_nameSubgoals_407_ == 0)
{
lean_object* v___x_471_; 
lean_inc(v_origTag_408_);
lean_inc(v___x_464_);
v___x_471_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_464_, v_fst_448_, v_fst_452_, v_fst_456_, v_snd_457_, v_origTag_408_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_425_ = v___x_471_;
goto v___jp_424_;
}
else
{
lean_object* v___x_472_; 
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
lean_inc(v_fst_452_);
v___x_472_ = lean_infer_type(v_fst_452_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
v___x_474_ = lean_whnf(v_a_473_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = l_Lean_Expr_bindingName_x21(v_a_475_);
lean_dec(v_a_475_);
lean_inc(v_origTag_408_);
v___x_477_ = l_Lean_Meta_appendTag(v_origTag_408_, v___x_476_);
lean_dec(v___x_476_);
lean_inc(v___x_464_);
v___x_478_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__1(v___x_464_, v_fst_448_, v_fst_452_, v_fst_456_, v_snd_457_, v___x_477_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_425_ = v___x_478_;
goto v___jp_424_;
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_dec(v_fst_452_);
lean_dec(v_fst_448_);
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_479_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_474_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_474_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_dec(v_fst_452_);
lean_dec(v_fst_448_);
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_487_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_472_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_472_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
}
case 4:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_del_object(v___x_459_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
v___x_517_ = lean_box(0);
v___x_518_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0(v_fst_456_, v_snd_457_, v_fst_452_, v_fst_448_, v___x_517_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
v___y_425_ = v___x_518_;
goto v___jp_424_;
}
case 5:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_inc(v___x_464_);
v___x_519_ = l_Lean_Expr_app___override(v_fst_452_, v___x_464_);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
lean_inc_ref(v___x_519_);
v___x_520_ = lean_infer_type(v___x_519_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_522_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___y_415_);
lean_inc_ref(v___y_414_);
v___x_522_ = lean_whnf(v_a_521_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l_Lean_Expr_bindingDomain_x21(v_a_523_);
lean_dec(v_a_523_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = 0;
v___x_527_ = lean_box(0);
v___x_528_ = l_Lean_Meta_mkFreshExprMVar(v___x_525_, v___x_526_, v___x_527_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_n(v_a_529_, 3);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = l_Lean_Expr_app___override(v_fst_448_, v_a_529_);
v___x_531_ = l_Lean_Expr_app___override(v___x_519_, v_a_529_);
v___x_532_ = l_Lean_Expr_mvarId_x21(v_a_529_);
lean_dec(v_a_529_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
v___x_534_ = lean_array_push(v_snd_457_, v___x_533_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_534_);
v___x_536_ = v___x_459_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_fst_456_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_543_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_538_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_536_);
lean_ctor_set(v___x_454_, 0, v___x_531_);
v___x_538_ = v___x_454_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_542_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_540_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_538_);
lean_ctor_set(v___x_450_, 0, v___x_530_);
v___x_540_ = v___x_450_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v_a_420_ = v___x_540_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v___x_519_);
lean_del_object(v___x_459_);
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
lean_dec(v_fst_448_);
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_544_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_528_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_528_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec_ref(v___x_519_);
lean_del_object(v___x_459_);
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
lean_dec(v_fst_448_);
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_552_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_522_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_522_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v___x_519_);
lean_del_object(v___x_459_);
lean_dec(v_snd_457_);
lean_dec(v_fst_456_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
lean_dec(v_fst_448_);
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_560_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_520_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_520_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
default: 
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_inc_n(v___x_464_, 2);
v___x_568_ = l_Lean_Expr_app___override(v_fst_448_, v___x_464_);
v___x_569_ = l_Lean_Expr_app___override(v_fst_452_, v___x_464_);
if (v_addImplicitArgs_411_ == 0)
{
uint8_t v___x_582_; 
v___x_582_ = l_Lean_Meta_ParamInfo_isExplicit(v___x_465_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_del_object(v___x_459_);
lean_del_object(v___x_454_);
lean_del_object(v___x_450_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_fst_456_);
lean_ctor_set(v___x_583_, 1, v_snd_457_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_569_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_568_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v_a_420_ = v___x_585_;
goto v___jp_419_;
}
else
{
goto v___jp_570_;
}
}
else
{
goto v___jp_570_;
}
v___jp_570_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_571_ = lean_box(0);
v___x_572_ = lean_array_push(v_fst_456_, v___x_571_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_572_);
v___x_574_ = v___x_459_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_snd_457_);
v___x_574_ = v_reuseFailAlloc_581_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_574_);
lean_ctor_set(v___x_454_, 0, v___x_569_);
v___x_576_ = v___x_454_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_580_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_578_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_576_);
lean_ctor_set(v___x_450_, 0, v___x_568_);
v___x_578_ = v___x_450_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v_a_420_ = v___x_578_;
goto v___jp_419_;
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
v___jp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_a_412_, v___x_421_);
lean_dec(v_a_412_);
v_a_412_ = v___x_422_;
v_b_413_ = v_a_420_;
goto _start;
}
v___jp_424_:
{
if (lean_obj_tag(v___y_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_435_; 
v_a_426_ = lean_ctor_get(v___y_425_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___y_425_);
if (v_isSharedCheck_435_ == 0)
{
v___x_428_ = v___y_425_;
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___y_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_435_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
if (lean_obj_tag(v_a_426_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; 
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_430_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v_a_426_, 1);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_a_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v_a_434_; 
lean_del_object(v___x_428_);
v_a_434_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v_a_426_, 1);
v_a_420_ = v_a_434_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
lean_dec(v_a_412_);
lean_dec(v_origTag_408_);
v_a_436_ = lean_ctor_get(v___y_425_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___y_425_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___y_425_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___y_425_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_405_ = stack[0].m_obj;
lean_object* v_args_406_ = stack[1].m_obj;
uint8_t v_nameSubgoals_407_ = stack[2].m_num;
lean_object* v_origTag_408_ = stack[3].m_obj;
lean_object* v_a_409_ = stack[4].m_obj;
lean_object* v___x_410_ = stack[5].m_obj;
uint8_t v_addImplicitArgs_411_ = stack[6].m_num;
lean_object* v_a_412_ = stack[7].m_obj;
lean_object* v_b_413_ = stack[8].m_obj;
lean_object* v___y_414_ = stack[9].m_obj;
lean_object* v___y_415_ = stack[10].m_obj;
lean_object* v___y_416_ = stack[11].m_obj;
lean_object* v___y_417_ = stack[12].m_obj;
lean_object* v_res_591_;
v_res_591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_405_, v_args_406_, v_nameSubgoals_407_, v_origTag_408_, v_a_409_, v___x_410_, v_addImplicitArgs_411_, v_a_412_, v_b_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___boxed(lean_object* v_upperBound_592_, lean_object* v_args_593_, lean_object* v_nameSubgoals_594_, lean_object* v_origTag_595_, lean_object* v_a_596_, lean_object* v___x_597_, lean_object* v_addImplicitArgs_598_, lean_object* v_a_599_, lean_object* v_b_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
uint8_t v_nameSubgoals_boxed_606_; uint8_t v_addImplicitArgs_boxed_607_; lean_object* v_res_608_; 
v_nameSubgoals_boxed_606_ = lean_unbox(v_nameSubgoals_594_);
v_addImplicitArgs_boxed_607_ = lean_unbox(v_addImplicitArgs_598_);
v_res_608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_592_, v_args_593_, v_nameSubgoals_boxed_606_, v_origTag_595_, v_a_596_, v___x_597_, v_addImplicitArgs_boxed_607_, v_a_599_, v_b_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___x_597_);
lean_dec_ref(v_a_596_);
lean_dec_ref(v_args_593_);
lean_dec(v_upperBound_592_);
return v_res_608_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(lean_object* v_a_609_, lean_object* v_b_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_array_616_; lean_object* v_start_617_; lean_object* v_stop_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_633_; 
v_array_616_ = lean_ctor_get(v_a_609_, 0);
v_start_617_ = lean_ctor_get(v_a_609_, 1);
v_stop_618_ = lean_ctor_get(v_a_609_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_609_);
if (v_isSharedCheck_633_ == 0)
{
v___x_620_ = v_a_609_;
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_stop_618_);
lean_inc(v_start_617_);
lean_inc(v_array_616_);
lean_dec(v_a_609_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_633_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_lt(v_start_617_, v_stop_618_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_del_object(v___x_620_);
lean_dec(v_stop_618_);
lean_dec(v_start_617_);
lean_dec_ref(v_array_616_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_b_610_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_start_617_, v___x_624_);
lean_inc_ref(v_array_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___x_625_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_array_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_stop_618_);
v___x_627_ = v_reuseFailAlloc_632_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_array_fget(v_array_616_, v_start_617_);
lean_dec(v_start_617_);
lean_dec_ref(v_array_616_);
v___x_629_ = l_Lean_Meta_mkCongrFun(v_b_610_, v___x_628_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v_a_609_ = v___x_627_;
v_b_610_ = v_a_630_;
goto _start;
}
else
{
lean_dec_ref(v___x_627_);
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_609_ = stack[0].m_obj;
lean_object* v_b_610_ = stack[1].m_obj;
lean_object* v___y_611_ = stack[2].m_obj;
lean_object* v___y_612_ = stack[3].m_obj;
lean_object* v___y_613_ = stack[4].m_obj;
lean_object* v___y_614_ = stack[5].m_obj;
lean_object* v_res_634_;
v_res_634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_609_, v_b_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg___boxed(lean_object* v_a_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_635_, v_b_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_642_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__2));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(lean_object* v_origTag_650_, lean_object* v_f_651_, lean_object* v_args_652_, uint8_t v_addImplicitArgs_653_, uint8_t v_nameSubgoals_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_proof_661_; lean_object* v_mvarIdsNew_662_; lean_object* v_mvarIdsNewInsts_663_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_array_get_size(v_args_652_);
lean_inc_ref(v_f_651_);
v___x_668_ = l_Lean_Meta_getFunInfoNArgs(v_f_651_, v___x_667_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
lean_inc_ref(v_f_651_);
v___x_670_ = l_Lean_Meta_getCongrSimpKinds(v_f_651_, v_a_669_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = 0;
lean_inc(v_a_669_);
lean_inc_ref(v_f_651_);
v___x_673_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_651_, v_a_669_, v_a_671_, v___x_672_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
if (lean_obj_tag(v_a_674_) == 1)
{
lean_object* v_val_675_; lean_object* v_proof_676_; lean_object* v_argKinds_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_val_675_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_val_675_);
lean_dec_ref_known(v_a_674_, 1);
v_proof_676_ = lean_ctor_get(v_val_675_, 1);
lean_inc_ref(v_proof_676_);
v_argKinds_677_ = lean_ctor_get(v_val_675_, 2);
lean_inc_ref(v_argKinds_677_);
lean_dec(v_val_675_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_array_get_size(v_argKinds_677_);
v___x_680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__1));
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_proof_676_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_f_651_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
lean_inc(v_origTag_650_);
v___x_683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v___x_679_, v_args_652_, v_nameSubgoals_654_, v_origTag_650_, v_a_669_, v_argKinds_677_, v_addImplicitArgs_653_, v___x_678_, v___x_682_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
lean_dec_ref(v_argKinds_677_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v_snd_685_; lean_object* v_snd_686_; lean_object* v_fst_687_; lean_object* v_fst_688_; lean_object* v_fst_689_; lean_object* v_snd_690_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v_lower_696_; lean_object* v_upper_697_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; uint8_t v___x_735_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v_snd_685_ = lean_ctor_get(v_a_684_, 1);
lean_inc(v_snd_685_);
v_snd_686_ = lean_ctor_get(v_snd_685_, 1);
lean_inc(v_snd_686_);
v_fst_687_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_fst_687_);
lean_dec(v_a_684_);
v_fst_688_ = lean_ctor_get(v_snd_685_, 0);
lean_inc(v_fst_688_);
lean_dec(v_snd_685_);
v_fst_689_ = lean_ctor_get(v_snd_686_, 0);
lean_inc(v_fst_689_);
v_snd_690_ = lean_ctor_get(v_snd_686_, 1);
lean_inc(v_snd_690_);
lean_dec(v_snd_686_);
v___x_735_ = lean_nat_dec_lt(v___x_679_, v___x_667_);
if (v___x_735_ == 0)
{
lean_dec(v_fst_687_);
lean_dec(v_a_669_);
lean_dec_ref(v_args_652_);
lean_dec(v_origTag_650_);
v_proof_661_ = v_fst_688_;
v_mvarIdsNew_662_ = v_fst_689_;
v_mvarIdsNewInsts_663_ = v_snd_690_;
goto v___jp_660_;
}
else
{
uint8_t v___x_736_; 
v___x_736_ = lean_nat_dec_eq(v___x_679_, v___x_678_);
if (v___x_736_ == 0)
{
v___y_729_ = v_a_655_;
v___y_730_ = v_a_656_;
v___y_731_ = v_a_657_;
v___y_732_ = v_a_658_;
goto v___jp_728_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_738_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_737_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_dec_ref_known(v___x_738_, 1);
v___y_729_ = v_a_655_;
v___y_730_ = v_a_656_;
v___y_731_ = v_a_657_;
v___y_732_ = v_a_658_;
goto v___jp_728_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_snd_690_);
lean_dec(v_fst_689_);
lean_dec(v_fst_688_);
lean_dec(v_fst_687_);
lean_dec(v_a_669_);
lean_dec_ref(v_args_652_);
lean_dec(v_origTag_650_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
v___jp_691_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = l_Array_toSubarray___redArg(v_args_652_, v_lower_696_, v_upper_697_);
lean_inc_ref(v___x_698_);
v___x_699_ = l_Subarray_copy___redArg(v___x_698_);
v___x_700_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_650_, v_fst_687_, v___x_699_, v_addImplicitArgs_653_, v_nameSubgoals_654_, v___y_692_, v___y_693_, v___y_695_, v___y_694_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v_snd_702_; lean_object* v_fst_703_; lean_object* v_fst_704_; lean_object* v_snd_705_; lean_object* v___x_706_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v_snd_702_ = lean_ctor_get(v_a_701_, 1);
lean_inc(v_snd_702_);
v_fst_703_ = lean_ctor_get(v_a_701_, 0);
lean_inc(v_fst_703_);
lean_dec(v_a_701_);
v_fst_704_ = lean_ctor_get(v_snd_702_, 0);
lean_inc(v_fst_704_);
v_snd_705_ = lean_ctor_get(v_snd_702_, 1);
lean_inc(v_snd_705_);
lean_dec(v_snd_702_);
v___x_706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_698_, v_fst_688_, v___y_692_, v___y_693_, v___y_695_, v___y_694_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_Meta_mkEqTrans(v_a_707_, v_fst_703_, v___y_692_, v___y_693_, v___y_695_, v___y_694_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = l_Array_append___redArg(v_fst_689_, v_fst_704_);
lean_dec(v_fst_704_);
v___x_711_ = l_Array_append___redArg(v_snd_690_, v_snd_705_);
lean_dec(v_snd_705_);
v_proof_661_ = v_a_709_;
v_mvarIdsNew_662_ = v___x_710_;
v_mvarIdsNewInsts_663_ = v___x_711_;
goto v___jp_660_;
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_snd_705_);
lean_dec(v_fst_704_);
lean_dec(v_snd_690_);
lean_dec(v_fst_689_);
v_a_712_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_708_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_snd_705_);
lean_dec(v_fst_704_);
lean_dec(v_fst_703_);
lean_dec(v_snd_690_);
lean_dec(v_fst_689_);
v_a_720_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_706_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_706_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_dec_ref(v___x_698_);
lean_dec(v_snd_690_);
lean_dec(v_fst_689_);
lean_dec(v_fst_688_);
return v___x_700_;
}
}
v___jp_728_:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = l_Lean_Meta_FunInfo_getArity(v_a_669_);
lean_dec(v_a_669_);
v___x_734_ = lean_nat_dec_le(v___x_733_, v___x_678_);
if (v___x_734_ == 0)
{
v___y_692_ = v___y_729_;
v___y_693_ = v___y_730_;
v___y_694_ = v___y_732_;
v___y_695_ = v___y_731_;
v_lower_696_ = v___x_733_;
v_upper_697_ = v___x_667_;
goto v___jp_691_;
}
else
{
lean_dec(v___x_733_);
v___y_692_ = v___y_729_;
v___y_693_ = v___y_730_;
v___y_694_ = v___y_732_;
v___y_695_ = v___y_731_;
v_lower_696_ = v___x_678_;
v_upper_697_ = v___x_667_;
goto v___jp_691_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_a_669_);
lean_dec_ref(v_args_652_);
lean_dec(v_origTag_650_);
v_a_747_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_683_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_683_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v_a_674_);
lean_dec(v_a_669_);
lean_dec_ref(v_args_652_);
lean_dec_ref(v_f_651_);
lean_dec(v_origTag_650_);
v___x_755_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___closed__3);
v___x_756_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_755_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
return v___x_756_;
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_669_);
lean_dec_ref(v_args_652_);
lean_dec_ref(v_f_651_);
lean_dec(v_origTag_650_);
v_a_757_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_673_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_673_);
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
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v_a_669_);
lean_dec_ref(v_args_652_);
lean_dec_ref(v_f_651_);
lean_dec(v_origTag_650_);
v_a_765_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_670_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_670_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_args_652_);
lean_dec_ref(v_f_651_);
lean_dec(v_origTag_650_);
v_a_773_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_668_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_668_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
v___jp_660_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_mvarIdsNew_662_);
lean_ctor_set(v___x_664_, 1, v_mvarIdsNewInsts_663_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v_proof_661_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_0interp(lean_interpreter_value* stack)
{
lean_object* v_origTag_650_ = stack[0].m_obj;
lean_object* v_f_651_ = stack[1].m_obj;
lean_object* v_args_652_ = stack[2].m_obj;
uint8_t v_addImplicitArgs_653_ = stack[3].m_num;
uint8_t v_nameSubgoals_654_ = stack[4].m_num;
lean_object* v_a_655_ = stack[5].m_obj;
lean_object* v_a_656_ = stack[6].m_obj;
lean_object* v_a_657_ = stack[7].m_obj;
lean_object* v_a_658_ = stack[8].m_obj;
lean_object* v_res_781_;
v_res_781_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_650_, v_f_651_, v_args_652_, v_addImplicitArgs_653_, v_nameSubgoals_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm___boxed(lean_object* v_origTag_782_, lean_object* v_f_783_, lean_object* v_args_784_, lean_object* v_addImplicitArgs_785_, lean_object* v_nameSubgoals_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
uint8_t v_addImplicitArgs_boxed_792_; uint8_t v_nameSubgoals_boxed_793_; lean_object* v_res_794_; 
v_addImplicitArgs_boxed_792_ = lean_unbox(v_addImplicitArgs_785_);
v_nameSubgoals_boxed_793_ = lean_unbox(v_nameSubgoals_786_);
v_res_794_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_origTag_782_, v_f_783_, v_args_784_, v_addImplicitArgs_boxed_792_, v_nameSubgoals_boxed_793_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
return v_res_794_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_object* v_inst_795_, lean_object* v_R_796_, lean_object* v_a_797_, lean_object* v_b_798_, lean_object* v_c_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v_a_797_, v_b_798_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v___x_805_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_797_ = stack[2].m_obj;
lean_object* v_b_798_ = stack[3].m_obj;
lean_object* v___y_800_ = stack[5].m_obj;
lean_object* v___y_801_ = stack[6].m_obj;
lean_object* v___y_802_ = stack[7].m_obj;
lean_object* v___y_803_ = stack[8].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(lean_box(0), lean_box(0), v_a_797_, v_b_798_, lean_box(0), v___y_800_, v___y_801_, v___y_802_, v___y_803_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___boxed(lean_object* v_inst_807_, lean_object* v_R_808_, lean_object* v_a_809_, lean_object* v_b_810_, lean_object* v_c_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0(v_inst_807_, v_R_808_, v_a_809_, v_b_810_, v_c_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
return v_res_817_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(lean_object* v_upperBound_818_, lean_object* v_args_819_, uint8_t v_nameSubgoals_820_, lean_object* v_origTag_821_, lean_object* v_a_822_, lean_object* v___x_823_, uint8_t v_addImplicitArgs_824_, lean_object* v_inst_825_, lean_object* v_R_826_, lean_object* v_a_827_, lean_object* v_b_828_, lean_object* v_c_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg(v_upperBound_818_, v_args_819_, v_nameSubgoals_820_, v_origTag_821_, v_a_822_, v___x_823_, v_addImplicitArgs_824_, v_a_827_, v_b_828_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_835_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_818_ = stack[0].m_obj;
lean_object* v_args_819_ = stack[1].m_obj;
uint8_t v_nameSubgoals_820_ = stack[2].m_num;
lean_object* v_origTag_821_ = stack[3].m_obj;
lean_object* v_a_822_ = stack[4].m_obj;
lean_object* v___x_823_ = stack[5].m_obj;
uint8_t v_addImplicitArgs_824_ = stack[6].m_num;
lean_object* v_a_827_ = stack[9].m_obj;
lean_object* v_b_828_ = stack[10].m_obj;
lean_object* v___y_830_ = stack[12].m_obj;
lean_object* v___y_831_ = stack[13].m_obj;
lean_object* v___y_832_ = stack[14].m_obj;
lean_object* v___y_833_ = stack[15].m_obj;
lean_object* v_res_836_;
v_res_836_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(v_upperBound_818_, v_args_819_, v_nameSubgoals_820_, v_origTag_821_, v_a_822_, v___x_823_, v_addImplicitArgs_824_, lean_box(0), lean_box(0), v_a_827_, v_b_828_, lean_box(0), v___y_830_, v___y_831_, v___y_832_, v___y_833_);
stack->m_obj
 = v_res_836_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_837_ = _args[0];
lean_object* v_args_838_ = _args[1];
lean_object* v_nameSubgoals_839_ = _args[2];
lean_object* v_origTag_840_ = _args[3];
lean_object* v_a_841_ = _args[4];
lean_object* v___x_842_ = _args[5];
lean_object* v_addImplicitArgs_843_ = _args[6];
lean_object* v_inst_844_ = _args[7];
lean_object* v_R_845_ = _args[8];
lean_object* v_a_846_ = _args[9];
lean_object* v_b_847_ = _args[10];
lean_object* v_c_848_ = _args[11];
lean_object* v___y_849_ = _args[12];
lean_object* v___y_850_ = _args[13];
lean_object* v___y_851_ = _args[14];
lean_object* v___y_852_ = _args[15];
lean_object* v___y_853_ = _args[16];
_start:
{
uint8_t v_nameSubgoals_boxed_854_; uint8_t v_addImplicitArgs_boxed_855_; lean_object* v_res_856_; 
v_nameSubgoals_boxed_854_ = lean_unbox(v_nameSubgoals_839_);
v_addImplicitArgs_boxed_855_ = lean_unbox(v_addImplicitArgs_843_);
v_res_856_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2(v_upperBound_837_, v_args_838_, v_nameSubgoals_boxed_854_, v_origTag_840_, v_a_841_, v___x_842_, v_addImplicitArgs_boxed_855_, v_inst_844_, v_R_845_, v_a_846_, v_b_847_, v_c_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec_ref(v___x_842_);
lean_dec_ref(v_a_841_);
lean_dec_ref(v_args_838_);
lean_dec(v_upperBound_837_);
return v_res_856_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__0));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__2));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__4));
v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
return v___x_865_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(lean_object* v_tacticName_866_, lean_object* v_rhs_867_, lean_object* v_rhs_x27_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; 
lean_inc_ref(v_rhs_x27_868_);
lean_inc_ref(v_rhs_867_);
v___x_874_ = l_Lean_Meta_isExprDefEqGuarded(v_rhs_867_, v_rhs_x27_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_896_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_896_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_896_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_896_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v___x_879_; 
v___x_879_ = lean_unbox(v_a_875_);
lean_dec(v_a_875_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_del_object(v___x_877_);
v___x_880_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_881_ = l_Lean_stringToMessageData(v_tacticName_866_);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__3);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
v___x_885_ = l_Lean_indentExpr(v_rhs_867_);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__5);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_indentExpr(v_rhs_x27_868_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_890_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
return v___x_891_;
}
else
{
lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec_ref(v_rhs_x27_868_);
lean_dec_ref(v_rhs_867_);
lean_dec_ref(v_tacticName_866_);
v___x_892_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_892_);
v___x_894_ = v___x_877_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_rhs_x27_868_);
lean_dec_ref(v_rhs_867_);
lean_dec_ref(v_tacticName_866_);
v_a_897_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_874_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_874_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_866_ = stack[0].m_obj;
lean_object* v_rhs_867_ = stack[1].m_obj;
lean_object* v_rhs_x27_868_ = stack[2].m_obj;
lean_object* v_a_869_ = stack[3].m_obj;
lean_object* v_a_870_ = stack[4].m_obj;
lean_object* v_a_871_ = stack[5].m_obj;
lean_object* v_a_872_ = stack[6].m_obj;
lean_object* v_res_905_;
v_res_905_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_866_, v_rhs_867_, v_rhs_x27_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
stack->m_obj
 = v_res_905_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___boxed(lean_object* v_tacticName_906_, lean_object* v_rhs_907_, lean_object* v_rhs_x27_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_906_, v_rhs_907_, v_rhs_x27_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_914_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__2));
v___x_920_ = l_Lean_stringToMessageData(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__4));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(lean_object* v_tacticName_924_, lean_object* v_rhs_925_, lean_object* v_proof_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; 
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
lean_inc_ref(v_a_927_);
v___x_932_ = lean_infer_type(v_proof_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
lean_inc_ref(v_a_927_);
v___x_934_ = lean_whnf(v_a_933_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__1));
v___x_937_ = lean_unsigned_to_nat(3u);
v___x_938_ = l_Lean_Expr_isAppOfArity(v_a_935_, v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_a_935_);
lean_dec_ref(v_rhs_925_);
v___x_939_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_940_ = l_Lean_stringToMessageData(v_tacticName_924_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__5);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_943_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = l_Lean_Expr_appArg_x21(v_a_935_);
lean_dec(v_a_935_);
v___x_946_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_924_, v_rhs_925_, v___x_945_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_946_;
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_rhs_925_);
lean_dec_ref(v_tacticName_924_);
v_a_947_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_934_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_934_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_dec_ref(v_rhs_925_);
lean_dec_ref(v_tacticName_924_);
v_a_955_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_932_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_932_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_924_ = stack[0].m_obj;
lean_object* v_rhs_925_ = stack[1].m_obj;
lean_object* v_proof_926_ = stack[2].m_obj;
lean_object* v_a_927_ = stack[3].m_obj;
lean_object* v_a_928_ = stack[4].m_obj;
lean_object* v_a_929_ = stack[5].m_obj;
lean_object* v_a_930_ = stack[6].m_obj;
lean_object* v_res_963_;
v_res_963_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_924_, v_rhs_925_, v_proof_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___boxed(lean_object* v_tacticName_964_, lean_object* v_rhs_965_, lean_object* v_proof_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_964_, v_rhs_965_, v_proof_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
return v_res_972_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(lean_object* v_e_973_, lean_object* v___y_974_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = l_Lean_Expr_hasMVar(v_e_973_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_e_973_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; lean_object* v_mctx_979_; lean_object* v___x_980_; lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_983_; lean_object* v_cache_984_; lean_object* v_zetaDeltaFVarIds_985_; lean_object* v_postponed_986_; lean_object* v_diag_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_996_; 
v___x_978_ = lean_st_ref_get(v___y_974_);
v_mctx_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_mctx_979_);
lean_dec(v___x_978_);
v___x_980_ = l_Lean_instantiateMVarsCore(v_mctx_979_, v_e_973_);
v_fst_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_fst_981_);
v_snd_982_ = lean_ctor_get(v___x_980_, 1);
lean_inc(v_snd_982_);
lean_dec_ref(v___x_980_);
v___x_983_ = lean_st_ref_take(v___y_974_);
v_cache_984_ = lean_ctor_get(v___x_983_, 1);
v_zetaDeltaFVarIds_985_ = lean_ctor_get(v___x_983_, 2);
v_postponed_986_ = lean_ctor_get(v___x_983_, 3);
v_diag_987_ = lean_ctor_get(v___x_983_, 4);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v___x_983_, 0);
lean_dec(v_unused_997_);
v___x_989_ = v___x_983_;
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_diag_987_);
lean_inc(v_postponed_986_);
lean_inc(v_zetaDeltaFVarIds_985_);
lean_inc(v_cache_984_);
lean_dec(v___x_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v_snd_982_);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_snd_982_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_cache_984_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_zetaDeltaFVarIds_985_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_postponed_986_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v_diag_987_);
v___x_992_ = v_reuseFailAlloc_995_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_st_ref_put(v___y_974_, v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_fst_981_);
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_973_ = stack[0].m_obj;
lean_object* v___y_974_ = stack[1].m_obj;
lean_object* v_res_998_;
v_res_998_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_973_, v___y_974_);
stack->m_obj
 = v_res_998_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg___boxed(lean_object* v_e_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_999_, v___y_1000_);
lean_dec(v___y_1000_);
return v_res_1002_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(lean_object* v_e_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_e_1003_, v___y_1005_);
return v___x_1009_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1003_ = stack[0].m_obj;
lean_object* v___y_1004_ = stack[1].m_obj;
lean_object* v___y_1005_ = stack[2].m_obj;
lean_object* v___y_1006_ = stack[3].m_obj;
lean_object* v___y_1007_ = stack[4].m_obj;
lean_object* v_res_1010_;
v_res_1010_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(v_e_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___boxed(lean_object* v_e_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0(v_e_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(lean_object* v_mvarId_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1025_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1025_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1018_ = stack[0].m_obj;
lean_object* v_x_1019_ = stack[1].m_obj;
lean_object* v___y_1020_ = stack[2].m_obj;
lean_object* v___y_1021_ = stack[3].m_obj;
lean_object* v___y_1022_ = stack[4].m_obj;
lean_object* v___y_1023_ = stack[5].m_obj;
lean_object* v_res_1042_;
v_res_1042_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
stack->m_obj
 = v_res_1042_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg___boxed(lean_object* v_mvarId_1043_, lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1043_, v_x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_object* v_00_u03b1_1051_, lean_object* v_mvarId_1052_, lean_object* v_x_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1052_, v_x_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1052_ = stack[1].m_obj;
lean_object* v_x_1053_ = stack[2].m_obj;
lean_object* v___y_1054_ = stack[3].m_obj;
lean_object* v___y_1055_ = stack[4].m_obj;
lean_object* v___y_1056_ = stack[5].m_obj;
lean_object* v___y_1057_ = stack[6].m_obj;
lean_object* v_res_1060_;
v_res_1060_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(lean_box(0), v_mvarId_1052_, v_x_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
stack->m_obj
 = v_res_1060_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_mvarId_1062_, lean_object* v_x_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3(v_00_u03b1_1061_, v_mvarId_1062_, v_x_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
if (lean_obj_tag(v_a_1070_) == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = l_List_reverse___redArg(v_a_1071_);
return v___x_1072_;
}
else
{
lean_object* v_head_1073_; lean_object* v_tail_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1083_; 
v_head_1073_ = lean_ctor_get(v_a_1070_, 0);
v_tail_1074_ = lean_ctor_get(v_a_1070_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_a_1070_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1076_ = v_a_1070_;
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_tail_1074_);
lean_inc(v_head_1073_);
lean_dec(v_a_1070_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1083_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v_head_1073_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v_a_1071_);
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_a_1071_);
v___x_1080_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
v_a_1070_ = v_tail_1074_;
v_a_1071_ = v___x_1080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v_ks_1088_; lean_object* v_vs_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1113_; 
v_ks_1088_ = lean_ctor_get(v_x_1084_, 0);
v_vs_1089_ = lean_ctor_get(v_x_1084_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1091_ = v_x_1084_;
v_isShared_1092_ = v_isSharedCheck_1113_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_vs_1089_);
lean_inc(v_ks_1088_);
lean_dec(v_x_1084_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1113_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = lean_array_get_size(v_ks_1088_);
v___x_1094_ = lean_nat_dec_lt(v_x_1085_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
lean_dec(v_x_1085_);
v___x_1095_ = lean_array_push(v_ks_1088_, v_x_1086_);
v___x_1096_ = lean_array_push(v_vs_1089_, v_x_1087_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1096_);
lean_ctor_set(v___x_1091_, 0, v___x_1095_);
v___x_1098_ = v___x_1091_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
lean_object* v_k_x27_1100_; uint8_t v___x_1101_; 
v_k_x27_1100_ = lean_array_fget_borrowed(v_ks_1088_, v_x_1085_);
v___x_1101_ = l_Lean_instBEqMVarId_beq(v_x_1086_, v_k_x27_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1103_; 
if (v_isShared_1092_ == 0)
{
v___x_1103_ = v___x_1091_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_ks_1088_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_vs_1089_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_x_1085_, v___x_1104_);
lean_dec(v_x_1085_);
v_x_1084_ = v___x_1103_;
v_x_1085_ = v___x_1105_;
goto _start;
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = lean_array_fset(v_ks_1088_, v_x_1085_, v_x_1086_);
v___x_1109_ = lean_array_fset(v_vs_1089_, v_x_1085_, v_x_1087_);
lean_dec(v_x_1085_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 1, v___x_1109_);
lean_ctor_set(v___x_1091_, 0, v___x_1108_);
v___x_1111_ = v___x_1091_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(lean_object* v_n_1114_, lean_object* v_k_1115_, lean_object* v_v_1116_){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_n_1114_, v___x_1117_, v_k_1115_, v_v_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1119_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(lean_object* v_x_1120_, size_t v_x_1121_, size_t v_x_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
if (lean_obj_tag(v_x_1120_) == 0)
{
lean_object* v_es_1125_; size_t v___x_1126_; size_t v___x_1127_; lean_object* v_j_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_es_1125_ = lean_ctor_get(v_x_1120_, 0);
v___x_1126_ = ((size_t)31ULL);
v___x_1127_ = lean_usize_land(v_x_1121_, v___x_1126_);
v_j_1128_ = lean_usize_to_nat(v___x_1127_);
v___x_1129_ = lean_array_get_size(v_es_1125_);
v___x_1130_ = lean_nat_dec_lt(v_j_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_dec(v_j_1128_);
lean_dec(v_x_1124_);
lean_dec(v_x_1123_);
return v_x_1120_;
}
else
{
lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1169_; 
lean_inc_ref(v_es_1125_);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1120_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_x_1120_, 0);
lean_dec(v_unused_1170_);
v___x_1132_ = v_x_1120_;
v_isShared_1133_ = v_isSharedCheck_1169_;
goto v_resetjp_1131_;
}
else
{
lean_dec(v_x_1120_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1169_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_v_1134_; lean_object* v___x_1135_; lean_object* v_xs_x27_1136_; lean_object* v___y_1138_; 
v_v_1134_ = lean_array_fget(v_es_1125_, v_j_1128_);
v___x_1135_ = lean_box(0);
v_xs_x27_1136_ = lean_array_fset(v_es_1125_, v_j_1128_, v___x_1135_);
switch(lean_obj_tag(v_v_1134_))
{
case 0:
{
lean_object* v_key_1143_; lean_object* v_val_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1154_; 
v_key_1143_ = lean_ctor_get(v_v_1134_, 0);
v_val_1144_ = lean_ctor_get(v_v_1134_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_v_1134_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1146_ = v_v_1134_;
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_val_1144_);
lean_inc(v_key_1143_);
lean_dec(v_v_1134_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___x_1148_; 
v___x_1148_ = l_Lean_instBEqMVarId_beq(v_x_1123_, v_key_1143_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_del_object(v___x_1146_);
v___x_1149_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1143_, v_val_1144_, v_x_1123_, v_x_1124_);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
v___y_1138_ = v___x_1150_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1152_; 
lean_dec(v_val_1144_);
lean_dec(v_key_1143_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v_x_1124_);
lean_ctor_set(v___x_1146_, 0, v_x_1123_);
v___x_1152_ = v___x_1146_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_x_1123_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_x_1124_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
v___y_1138_ = v___x_1152_;
goto v___jp_1137_;
}
}
}
}
case 1:
{
lean_object* v_node_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1167_; 
v_node_1155_ = lean_ctor_get(v_v_1134_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_v_1134_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1157_ = v_v_1134_;
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_node_1155_);
lean_dec(v_v_1134_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1159_ = ((size_t)5ULL);
v___x_1160_ = lean_usize_shift_right(v_x_1121_, v___x_1159_);
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_add(v_x_1122_, v___x_1161_);
v___x_1163_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_node_1155_, v___x_1160_, v___x_1162_, v_x_1123_, v_x_1124_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1163_);
v___x_1165_ = v___x_1157_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
v___y_1138_ = v___x_1165_;
goto v___jp_1137_;
}
}
}
default: 
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_x_1123_);
lean_ctor_set(v___x_1168_, 1, v_x_1124_);
v___y_1138_ = v___x_1168_;
goto v___jp_1137_;
}
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_array_fset(v_xs_x27_1136_, v_j_1128_, v___y_1138_);
lean_dec(v_j_1128_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1139_);
v___x_1141_ = v___x_1132_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_ks_1171_; lean_object* v_vs_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1190_; 
v_ks_1171_ = lean_ctor_get(v_x_1120_, 0);
v_vs_1172_ = lean_ctor_get(v_x_1120_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_x_1120_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1174_ = v_x_1120_;
v_isShared_1175_ = v_isSharedCheck_1190_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_vs_1172_);
lean_inc(v_ks_1171_);
lean_dec(v_x_1120_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1190_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_ks_1171_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_vs_1172_);
v___x_1177_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v_newNode_1178_; size_t v___x_1179_; uint8_t v___x_1180_; 
v_newNode_1178_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v___x_1177_, v_x_1123_, v_x_1124_);
v___x_1179_ = ((size_t)7ULL);
v___x_1180_ = lean_usize_dec_le(v___x_1179_, v_x_1122_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1178_);
v___x_1182_ = lean_unsigned_to_nat(4u);
v___x_1183_ = lean_nat_dec_lt(v___x_1181_, v___x_1182_);
lean_dec(v___x_1181_);
if (v___x_1183_ == 0)
{
lean_object* v_ks_1184_; lean_object* v_vs_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_ks_1184_ = lean_ctor_get(v_newNode_1178_, 0);
lean_inc_ref(v_ks_1184_);
v_vs_1185_ = lean_ctor_get(v_newNode_1178_, 1);
lean_inc_ref(v_vs_1185_);
lean_dec_ref(v_newNode_1178_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_1188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_x_1122_, v_ks_1184_, v_vs_1185_, v___x_1186_, v___x_1187_);
lean_dec_ref(v_vs_1185_);
lean_dec_ref(v_ks_1184_);
return v___x_1188_;
}
else
{
return v_newNode_1178_;
}
}
else
{
return v_newNode_1178_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1120_ = stack[0].m_obj;
size_t v_x_1121_ = stack[1].m_num;
size_t v_x_1122_ = stack[2].m_num;
lean_object* v_x_1123_ = stack[3].m_obj;
lean_object* v_x_1124_ = stack[4].m_obj;
lean_object* v_res_1191_;
v_res_1191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1120_, v_x_1121_, v_x_1122_, v_x_1123_, v_x_1124_);
stack->m_obj
 = v_res_1191_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(size_t v_depth_1192_, lean_object* v_keys_1193_, lean_object* v_vals_1194_, lean_object* v_i_1195_, lean_object* v_entries_1196_){
_start:
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_array_get_size(v_keys_1193_);
v___x_1198_ = lean_nat_dec_lt(v_i_1195_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec(v_i_1195_);
return v_entries_1196_;
}
else
{
lean_object* v_k_1199_; lean_object* v_v_1200_; uint64_t v___x_1201_; size_t v_h_1202_; size_t v___x_1203_; lean_object* v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; size_t v_h_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_k_1199_ = lean_array_fget_borrowed(v_keys_1193_, v_i_1195_);
v_v_1200_ = lean_array_fget_borrowed(v_vals_1194_, v_i_1195_);
v___x_1201_ = l_Lean_instHashableMVarId_hash(v_k_1199_);
v_h_1202_ = lean_uint64_to_usize(v___x_1201_);
v___x_1203_ = ((size_t)5ULL);
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_sub(v_depth_1192_, v___x_1205_);
v___x_1207_ = lean_usize_mul(v___x_1203_, v___x_1206_);
v_h_1208_ = lean_usize_shift_right(v_h_1202_, v___x_1207_);
v___x_1209_ = lean_nat_add(v_i_1195_, v___x_1204_);
lean_dec(v_i_1195_);
lean_inc(v_v_1200_);
lean_inc(v_k_1199_);
v___x_1210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_entries_1196_, v_h_1208_, v_depth_1192_, v_k_1199_, v_v_1200_);
v_i_1195_ = v___x_1209_;
v_entries_1196_ = v___x_1210_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1192_ = stack[0].m_num;
lean_object* v_keys_1193_ = stack[1].m_obj;
lean_object* v_vals_1194_ = stack[2].m_obj;
lean_object* v_i_1195_ = stack[3].m_obj;
lean_object* v_entries_1196_ = stack[4].m_obj;
lean_object* v_res_1212_;
v_res_1212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_1192_, v_keys_1193_, v_vals_1194_, v_i_1195_, v_entries_1196_);
stack->m_obj
 = v_res_1212_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1213_, lean_object* v_keys_1214_, lean_object* v_vals_1215_, lean_object* v_i_1216_, lean_object* v_entries_1217_){
_start:
{
size_t v_depth_boxed_1218_; lean_object* v_res_1219_; 
v_depth_boxed_1218_ = lean_unbox_usize(v_depth_1213_);
lean_dec(v_depth_1213_);
v_res_1219_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_boxed_1218_, v_keys_1214_, v_vals_1215_, v_i_1216_, v_entries_1217_);
lean_dec_ref(v_vals_1215_);
lean_dec_ref(v_keys_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
size_t v_x_2844__boxed_1225_; size_t v_x_2845__boxed_1226_; lean_object* v_res_1227_; 
v_x_2844__boxed_1225_ = lean_unbox_usize(v_x_1221_);
lean_dec(v_x_1221_);
v_x_2845__boxed_1226_ = lean_unbox_usize(v_x_1222_);
lean_dec(v_x_1222_);
v_res_1227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1220_, v_x_2844__boxed_1225_, v_x_2845__boxed_1226_, v_x_1223_, v_x_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(lean_object* v_x_1228_, lean_object* v_x_1229_, lean_object* v_x_1230_){
_start:
{
uint64_t v___x_1231_; size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = l_Lean_instHashableMVarId_hash(v_x_1229_);
v___x_1232_ = lean_uint64_to_usize(v___x_1231_);
v___x_1233_ = ((size_t)1ULL);
v___x_1234_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1228_, v___x_1232_, v___x_1233_, v_x_1229_, v_x_1230_);
return v___x_1234_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(lean_object* v_mvarId_1235_, lean_object* v_val_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v_mctx_1240_; lean_object* v_cache_1241_; lean_object* v_zetaDeltaFVarIds_1242_; lean_object* v_postponed_1243_; lean_object* v_diag_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1274_; 
v___x_1239_ = lean_st_ref_take(v___y_1237_);
v_mctx_1240_ = lean_ctor_get(v___x_1239_, 0);
v_cache_1241_ = lean_ctor_get(v___x_1239_, 1);
v_zetaDeltaFVarIds_1242_ = lean_ctor_get(v___x_1239_, 2);
v_postponed_1243_ = lean_ctor_get(v___x_1239_, 3);
v_diag_1244_ = lean_ctor_get(v___x_1239_, 4);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1246_ = v___x_1239_;
v_isShared_1247_ = v_isSharedCheck_1274_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_diag_1244_);
lean_inc(v_postponed_1243_);
lean_inc(v_zetaDeltaFVarIds_1242_);
lean_inc(v_cache_1241_);
lean_inc(v_mctx_1240_);
lean_dec(v___x_1239_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1274_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v_depth_1248_; lean_object* v_levelAssignDepth_1249_; lean_object* v_lmvarCounter_1250_; lean_object* v_mvarCounter_1251_; lean_object* v_lDecls_1252_; lean_object* v_decls_1253_; lean_object* v_userNames_1254_; lean_object* v_lAssignment_1255_; lean_object* v_eAssignment_1256_; lean_object* v_dAssignment_1257_; lean_object* v_instanceTypedMVars_1258_; lean_object* v_synthNormMemo_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1273_; 
v_depth_1248_ = lean_ctor_get(v_mctx_1240_, 0);
v_levelAssignDepth_1249_ = lean_ctor_get(v_mctx_1240_, 1);
v_lmvarCounter_1250_ = lean_ctor_get(v_mctx_1240_, 2);
v_mvarCounter_1251_ = lean_ctor_get(v_mctx_1240_, 3);
v_lDecls_1252_ = lean_ctor_get(v_mctx_1240_, 4);
v_decls_1253_ = lean_ctor_get(v_mctx_1240_, 5);
v_userNames_1254_ = lean_ctor_get(v_mctx_1240_, 6);
v_lAssignment_1255_ = lean_ctor_get(v_mctx_1240_, 7);
v_eAssignment_1256_ = lean_ctor_get(v_mctx_1240_, 8);
v_dAssignment_1257_ = lean_ctor_get(v_mctx_1240_, 9);
v_instanceTypedMVars_1258_ = lean_ctor_get(v_mctx_1240_, 10);
v_synthNormMemo_1259_ = lean_ctor_get(v_mctx_1240_, 11);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_mctx_1240_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1261_ = v_mctx_1240_;
v_isShared_1262_ = v_isSharedCheck_1273_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_synthNormMemo_1259_);
lean_inc(v_instanceTypedMVars_1258_);
lean_inc(v_dAssignment_1257_);
lean_inc(v_eAssignment_1256_);
lean_inc(v_lAssignment_1255_);
lean_inc(v_userNames_1254_);
lean_inc(v_decls_1253_);
lean_inc(v_lDecls_1252_);
lean_inc(v_mvarCounter_1251_);
lean_inc(v_lmvarCounter_1250_);
lean_inc(v_levelAssignDepth_1249_);
lean_inc(v_depth_1248_);
lean_dec(v_mctx_1240_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1273_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1263_ = lean_box(0);
v___x_1264_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_1256_, v_mvarId_1235_, v_val_1236_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 8, v___x_1264_);
v___x_1266_ = v___x_1261_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_depth_1248_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_levelAssignDepth_1249_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_lmvarCounter_1250_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_mvarCounter_1251_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_lDecls_1252_);
lean_ctor_set(v_reuseFailAlloc_1272_, 5, v_decls_1253_);
lean_ctor_set(v_reuseFailAlloc_1272_, 6, v_userNames_1254_);
lean_ctor_set(v_reuseFailAlloc_1272_, 7, v_lAssignment_1255_);
lean_ctor_set(v_reuseFailAlloc_1272_, 8, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1272_, 9, v_dAssignment_1257_);
lean_ctor_set(v_reuseFailAlloc_1272_, 10, v_instanceTypedMVars_1258_);
lean_ctor_set(v_reuseFailAlloc_1272_, 11, v_synthNormMemo_1259_);
v___x_1266_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1268_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1266_);
v___x_1268_ = v___x_1246_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_cache_1241_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_zetaDeltaFVarIds_1242_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_postponed_1243_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_diag_1244_);
v___x_1268_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_st_ref_put(v___y_1237_, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1263_);
return v___x_1270_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1235_ = stack[0].m_obj;
lean_object* v_val_1236_ = stack[1].m_obj;
lean_object* v___y_1237_ = stack[2].m_obj;
lean_object* v_res_1275_;
v_res_1275_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1235_, v_val_1236_, v___y_1237_);
stack->m_obj
 = v_res_1275_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg___boxed(lean_object* v_mvarId_1276_, lean_object* v_val_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1276_, v_val_1277_, v___y_1278_);
lean_dec(v___y_1278_);
return v_res_1280_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__0));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1284_; lean_object* v_dummy_1285_; 
v___x_1284_ = lean_box(0);
v_dummy_1285_ = l_Lean_Expr_sort___override(v___x_1284_);
return v_dummy_1285_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0(lean_object* v_mvarId_1287_, uint8_t v_addImplicitArgs_1288_, uint8_t v_nameSubgoals_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
lean_inc(v_mvarId_1287_);
v___x_1295_ = l_Lean_MVarId_getTag(v_mvarId_1287_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1297_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
lean_inc(v_mvarId_1287_);
v___x_1297_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1287_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1387_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v_fst_1299_ = lean_ctor_get(v_a_1298_, 0);
v_snd_1300_ = lean_ctor_get(v_a_1298_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_a_1298_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1302_ = v_a_1298_;
v_isShared_1303_ = v_isSharedCheck_1387_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_inc(v_fst_1299_);
lean_dec(v_a_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1387_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v_a_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1304_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1299_, v___y_1291_);
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1304_);
v___x_1306_ = l_Lean_Expr_cleanupAnnotations(v_a_1305_);
v___x_1307_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_isImplies(v___x_1306_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; uint8_t v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = lean_unbox(v_a_1308_);
lean_dec(v_a_1308_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_Expr_isApp(v___x_1306_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec(v_snd_1300_);
lean_dec(v_a_1296_);
lean_dec(v_mvarId_1287_);
v___x_1311_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__1);
v___x_1312_ = l_Lean_indentExpr(v___x_1306_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 7);
lean_ctor_set(v___x_1302_, 1, v___x_1312_);
lean_ctor_set(v___x_1302_, 0, v___x_1311_);
v___x_1314_ = v___x_1302_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1314_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1317_; lean_object* v_dummy_1318_; lean_object* v_nargs_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_del_object(v___x_1302_);
v___x_1317_ = l_Lean_Expr_getAppFn(v___x_1306_);
v_dummy_1318_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1319_ = l_Lean_Expr_getAppNumArgs(v___x_1306_);
lean_inc(v_nargs_1319_);
v___x_1320_ = lean_mk_array(v_nargs_1319_, v_dummy_1318_);
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = lean_nat_sub(v_nargs_1319_, v___x_1321_);
lean_dec(v_nargs_1319_);
v___x_1323_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_1306_, v___x_1320_, v___x_1322_);
v___x_1324_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm(v_a_1296_, v___x_1317_, v___x_1323_, v_addImplicitArgs_1288_, v_nameSubgoals_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v_snd_1326_; lean_object* v_fst_1327_; lean_object* v_fst_1328_; lean_object* v_snd_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v_snd_1326_ = lean_ctor_get(v_a_1325_, 1);
lean_inc(v_snd_1326_);
v_fst_1327_ = lean_ctor_get(v_a_1325_, 0);
lean_inc_n(v_fst_1327_, 2);
lean_dec(v_a_1325_);
v_fst_1328_ = lean_ctor_get(v_snd_1326_, 0);
lean_inc(v_fst_1328_);
v_snd_1329_ = lean_ctor_get(v_snd_1326_, 1);
lean_inc(v_snd_1329_);
lean_dec(v_snd_1326_);
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__3));
v___x_1331_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v___x_1330_, v_snd_1300_, v_fst_1327_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref_known(v___x_1331_, 1);
v___x_1332_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1287_, v_fst_1327_, v___y_1291_);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v___x_1332_, 0);
lean_dec(v_unused_1343_);
v___x_1334_ = v___x_1332_;
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
else
{
lean_dec(v___x_1332_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1342_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1336_ = lean_array_to_list(v_fst_1328_);
v___x_1337_ = lean_array_to_list(v_snd_1329_);
v___x_1338_ = l_List_appendTR___redArg(v___x_1336_, v___x_1337_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1340_ = v___x_1334_;
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
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_snd_1329_);
lean_dec(v_fst_1328_);
lean_dec(v_fst_1327_);
lean_dec(v_mvarId_1287_);
v_a_1344_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1331_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1331_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_snd_1300_);
lean_dec(v_mvarId_1287_);
v_a_1352_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1324_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1324_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
else
{
lean_object* v___x_1360_; 
lean_dec_ref(v___x_1306_);
lean_del_object(v___x_1302_);
lean_dec(v_snd_1300_);
lean_dec(v_a_1296_);
v___x_1360_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies(v_mvarId_1287_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1370_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1370_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1365_ = lean_box(0);
v___x_1366_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Conv_congr_spec__2(v_a_1361_, v___x_1365_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1366_);
v___x_1368_ = v___x_1363_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_a_1371_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1360_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1360_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec_ref(v___x_1306_);
lean_del_object(v___x_1302_);
lean_dec(v_snd_1300_);
lean_dec(v_a_1296_);
lean_dec(v_mvarId_1287_);
v_a_1379_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1307_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1307_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_a_1296_);
lean_dec(v_mvarId_1287_);
v_a_1388_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1297_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1297_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v_mvarId_1287_);
v_a_1396_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1295_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1295_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1287_ = stack[0].m_obj;
uint8_t v_addImplicitArgs_1288_ = stack[1].m_num;
uint8_t v_nameSubgoals_1289_ = stack[2].m_num;
lean_object* v___y_1290_ = stack[3].m_obj;
lean_object* v___y_1291_ = stack[4].m_obj;
lean_object* v___y_1292_ = stack[5].m_obj;
lean_object* v___y_1293_ = stack[6].m_obj;
lean_object* v_res_1404_;
v_res_1404_ = l_Lean_Elab_Tactic_Conv_congr___lam__0(v_mvarId_1287_, v_addImplicitArgs_1288_, v_nameSubgoals_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
stack->m_obj
 = v_res_1404_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed(lean_object* v_mvarId_1405_, lean_object* v_addImplicitArgs_1406_, lean_object* v_nameSubgoals_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1413_; uint8_t v_nameSubgoals_boxed_1414_; lean_object* v_res_1415_; 
v_addImplicitArgs_boxed_1413_ = lean_unbox(v_addImplicitArgs_1406_);
v_nameSubgoals_boxed_1414_ = lean_unbox(v_nameSubgoals_1407_);
v_res_1415_ = l_Lean_Elab_Tactic_Conv_congr___lam__0(v_mvarId_1405_, v_addImplicitArgs_boxed_1413_, v_nameSubgoals_boxed_1414_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1415_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congr(lean_object* v_mvarId_1416_, uint8_t v_addImplicitArgs_1417_, uint8_t v_nameSubgoals_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___f_1426_; lean_object* v___x_1427_; 
v___x_1424_ = lean_box(v_addImplicitArgs_1417_);
v___x_1425_ = lean_box(v_nameSubgoals_1418_);
lean_inc(v_mvarId_1416_);
v___f_1426_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1426_, 0, v_mvarId_1416_);
lean_closure_set(v___f_1426_, 1, v___x_1424_);
lean_closure_set(v___f_1426_, 2, v___x_1425_);
v___x_1427_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1416_, v___f_1426_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
return v___x_1427_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congr_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1416_ = stack[0].m_obj;
uint8_t v_addImplicitArgs_1417_ = stack[1].m_num;
uint8_t v_nameSubgoals_1418_ = stack[2].m_num;
lean_object* v_a_1419_ = stack[3].m_obj;
lean_object* v_a_1420_ = stack[4].m_obj;
lean_object* v_a_1421_ = stack[5].m_obj;
lean_object* v_a_1422_ = stack[6].m_obj;
lean_object* v_res_1428_;
v_res_1428_ = l_Lean_Elab_Tactic_Conv_congr(v_mvarId_1416_, v_addImplicitArgs_1417_, v_nameSubgoals_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
stack->m_obj
 = v_res_1428_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congr___boxed(lean_object* v_mvarId_1429_, lean_object* v_addImplicitArgs_1430_, lean_object* v_nameSubgoals_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
uint8_t v_addImplicitArgs_boxed_1437_; uint8_t v_nameSubgoals_boxed_1438_; lean_object* v_res_1439_; 
v_addImplicitArgs_boxed_1437_ = lean_unbox(v_addImplicitArgs_1430_);
v_nameSubgoals_boxed_1438_ = lean_unbox(v_nameSubgoals_1431_);
v_res_1439_ = l_Lean_Elab_Tactic_Conv_congr(v_mvarId_1429_, v_addImplicitArgs_boxed_1437_, v_nameSubgoals_boxed_1438_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
return v_res_1439_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(lean_object* v_mvarId_1440_, lean_object* v_val_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1440_, v_val_1441_, v___y_1443_);
return v___x_1447_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1440_ = stack[0].m_obj;
lean_object* v_val_1441_ = stack[1].m_obj;
lean_object* v___y_1442_ = stack[2].m_obj;
lean_object* v___y_1443_ = stack[3].m_obj;
lean_object* v___y_1444_ = stack[4].m_obj;
lean_object* v___y_1445_ = stack[5].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(v_mvarId_1440_, v_val_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___boxed(lean_object* v_mvarId_1449_, lean_object* v_val_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1(v_mvarId_1449_, v_val_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1(lean_object* v_00_u03b2_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_x_1458_, v_x_1459_, v_x_1460_);
return v___x_1461_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1462_, lean_object* v_x_1463_, size_t v_x_1464_, size_t v_x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___redArg(v_x_1463_, v_x_1464_, v_x_1465_, v_x_1466_, v_x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1463_ = stack[1].m_obj;
size_t v_x_1464_ = stack[2].m_num;
size_t v_x_1465_ = stack[3].m_num;
lean_object* v_x_1466_ = stack[4].m_obj;
lean_object* v_x_1467_ = stack[5].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(lean_box(0), v_x_1463_, v_x_1464_, v_x_1465_, v_x_1466_, v_x_1467_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_){
_start:
{
size_t v_x_3595__boxed_1476_; size_t v_x_3596__boxed_1477_; lean_object* v_res_1478_; 
v_x_3595__boxed_1476_ = lean_unbox_usize(v_x_1472_);
lean_dec(v_x_1472_);
v_x_3596__boxed_1477_ = lean_unbox_usize(v_x_1473_);
lean_dec(v_x_1473_);
v_res_1478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3(v_00_u03b2_1470_, v_x_1471_, v_x_3595__boxed_1476_, v_x_3596__boxed_1477_, v_x_1474_, v_x_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_1479_, lean_object* v_n_1480_, lean_object* v_k_1481_, lean_object* v_v_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5___redArg(v_n_1480_, v_k_1481_, v_v_1482_);
return v___x_1483_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1484_, size_t v_depth_1485_, lean_object* v_keys_1486_, lean_object* v_vals_1487_, lean_object* v_heq_1488_, lean_object* v_i_1489_, lean_object* v_entries_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___redArg(v_depth_1485_, v_keys_1486_, v_vals_1487_, v_i_1489_, v_entries_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1485_ = stack[1].m_num;
lean_object* v_keys_1486_ = stack[2].m_obj;
lean_object* v_vals_1487_ = stack[3].m_obj;
lean_object* v_i_1489_ = stack[5].m_obj;
lean_object* v_entries_1490_ = stack[6].m_obj;
lean_object* v_res_1492_;
v_res_1492_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(lean_box(0), v_depth_1485_, v_keys_1486_, v_vals_1487_, lean_box(0), v_i_1489_, v_entries_1490_);
stack->m_obj
 = v_res_1492_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1493_, lean_object* v_depth_1494_, lean_object* v_keys_1495_, lean_object* v_vals_1496_, lean_object* v_heq_1497_, lean_object* v_i_1498_, lean_object* v_entries_1499_){
_start:
{
size_t v_depth_boxed_1500_; lean_object* v_res_1501_; 
v_depth_boxed_1500_ = lean_unbox_usize(v_depth_1494_);
lean_dec(v_depth_1494_);
v_res_1501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__6(v_00_u03b2_1493_, v_depth_boxed_1500_, v_keys_1495_, v_vals_1496_, v_heq_1497_, v_i_1498_, v_entries_1499_);
lean_dec_ref(v_vals_1496_);
lean_dec_ref(v_keys_1495_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_1502_, lean_object* v_x_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1_spec__3_spec__5_spec__6___redArg(v_x_1503_, v_x_1504_, v_x_1505_, v_x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
if (lean_obj_tag(v_a_1508_) == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_array_to_list(v_a_1509_);
return v___x_1510_;
}
else
{
lean_object* v_head_1511_; 
v_head_1511_ = lean_ctor_get(v_a_1508_, 0);
if (lean_obj_tag(v_head_1511_) == 0)
{
lean_object* v_tail_1512_; 
v_tail_1512_ = lean_ctor_get(v_a_1508_, 1);
lean_inc(v_tail_1512_);
lean_dec_ref_known(v_a_1508_, 2);
v_a_1508_ = v_tail_1512_;
goto _start;
}
else
{
lean_object* v_tail_1514_; lean_object* v_val_1515_; lean_object* v___x_1516_; 
lean_inc_ref(v_head_1511_);
v_tail_1514_ = lean_ctor_get(v_a_1508_, 1);
lean_inc(v_tail_1514_);
lean_dec_ref_known(v_a_1508_, 2);
v_val_1515_ = lean_ctor_get(v_head_1511_, 0);
lean_inc(v_val_1515_);
lean_dec_ref_known(v_head_1511_, 1);
v___x_1516_ = lean_array_push(v_a_1509_, v_val_1515_);
v_a_1508_ = v_tail_1514_;
v_a_1509_ = v___x_1516_;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg(lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; uint8_t v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = 0;
v___x_1529_ = 1;
v___x_1530_ = l_Lean_Elab_Tactic_Conv_congr(v_a_1527_, v___x_1528_, v___x_1529_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalCongr___redArg___closed__0));
v___x_1533_ = l_List_filterMapTR_go___at___00Lean_Elab_Tactic_Conv_evalCongr_spec__0(v_a_1531_, v___x_1532_);
v___x_1534_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_1533_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
return v___x_1534_;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1530_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1530_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
v_a_1543_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1526_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1526_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalCongr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1520_ = stack[0].m_obj;
lean_object* v_a_1521_ = stack[1].m_obj;
lean_object* v_a_1522_ = stack[2].m_obj;
lean_object* v_a_1523_ = stack[3].m_obj;
lean_object* v_a_1524_ = stack[4].m_obj;
lean_object* v_res_1551_;
v_res_1551_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_);
stack->m_obj
 = v_res_1551_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___redArg___boxed(lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec(v_a_1556_);
lean_dec_ref(v_a_1555_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
return v_res_1558_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalCongr(lean_object* v_x_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Elab_Tactic_Conv_evalCongr___redArg(v_a_1561_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1559_ = stack[0].m_obj;
lean_object* v_a_1560_ = stack[1].m_obj;
lean_object* v_a_1561_ = stack[2].m_obj;
lean_object* v_a_1562_ = stack[3].m_obj;
lean_object* v_a_1563_ = stack[4].m_obj;
lean_object* v_a_1564_ = stack[5].m_obj;
lean_object* v_a_1565_ = stack[6].m_obj;
lean_object* v_a_1566_ = stack[7].m_obj;
lean_object* v_a_1567_ = stack[8].m_obj;
lean_object* v_res_1570_;
v_res_1570_ = l_Lean_Elab_Tactic_Conv_evalCongr(v_x_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_);
stack->m_obj
 = v_res_1570_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalCongr___boxed(lean_object* v_x_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Elab_Tactic_Conv_evalCongr(v_x_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec_ref(v_a_1572_);
lean_dec(v_x_1571_);
return v_res_1581_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1(){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1596_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1597_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__0));
v___x_1598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1599_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalCongr___boxed), 10, 0);
v___x_1600_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1596_, v___x_1597_, v___x_1598_, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1601_;
v_res_1601_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
stack->m_obj
 = v_res_1601_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___boxed(lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1();
return v_res_1603_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3(){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr__1___closed__2));
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___closed__6));
v___x_1632_ = l_Lean_addBuiltinDeclarationRanges(v___x_1630_, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1633_;
v_res_1633_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
stack->m_obj
 = v_res_1633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3___boxed(lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalCongr___regBuiltin_Lean_Elab_Tactic_Conv_evalCongr_declRange__3();
return v_res_1635_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(lean_object* v_as_1636_, size_t v_i_1637_, size_t v_stop_1638_, lean_object* v_b_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_eq(v_i_1637_, v_stop_1638_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_array_uget_borrowed(v_as_1636_, v_i_1637_);
lean_inc(v___x_1646_);
v___x_1647_ = l_Lean_Meta_mkCongrFun(v_b_1639_, v___x_1646_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; size_t v___x_1649_; size_t v___x_1650_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = ((size_t)1ULL);
v___x_1650_ = lean_usize_add(v_i_1637_, v___x_1649_);
v_i_1637_ = v___x_1650_;
v_b_1639_ = v_a_1648_;
goto _start;
}
else
{
return v___x_1647_;
}
}
else
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_b_1639_);
return v___x_1652_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1636_ = stack[0].m_obj;
size_t v_i_1637_ = stack[1].m_num;
size_t v_stop_1638_ = stack[2].m_num;
lean_object* v_b_1639_ = stack[3].m_obj;
lean_object* v___y_1640_ = stack[4].m_obj;
lean_object* v___y_1641_ = stack[5].m_obj;
lean_object* v___y_1642_ = stack[6].m_obj;
lean_object* v___y_1643_ = stack[7].m_obj;
lean_object* v_res_1653_;
v_res_1653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_as_1636_, v_i_1637_, v_stop_1638_, v_b_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
stack->m_obj
 = v_res_1653_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0___boxed(lean_object* v_as_1654_, lean_object* v_i_1655_, lean_object* v_stop_1656_, lean_object* v_b_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
size_t v_i_boxed_1663_; size_t v_stop_boxed_1664_; lean_object* v_res_1665_; 
v_i_boxed_1663_ = lean_unbox_usize(v_i_1655_);
lean_dec(v_i_1655_);
v_stop_boxed_1664_ = lean_unbox_usize(v_stop_1656_);
lean_dec(v_stop_1656_);
v_res_1665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_as_1654_, v_i_boxed_1663_, v_stop_boxed_1664_, v_b_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v_as_1654_);
return v_res_1665_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(lean_object* v_mvarId_1667_, lean_object* v_snd_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
if (lean_obj_tag(v_x_1669_) == 5)
{
lean_object* v_fn_1677_; lean_object* v_arg_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_fn_1677_ = lean_ctor_get(v_x_1669_, 0);
lean_inc_ref(v_fn_1677_);
v_arg_1678_ = lean_ctor_get(v_x_1669_, 1);
lean_inc_ref(v_arg_1678_);
lean_dec_ref_known(v_x_1669_, 2);
v___x_1679_ = lean_array_set(v_x_1670_, v_x_1671_, v_arg_1678_);
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_sub(v_x_1671_, v___x_1680_);
lean_dec(v_x_1671_);
v_x_1669_ = v_fn_1677_;
v_x_1670_ = v___x_1679_;
v_x_1671_ = v___x_1681_;
goto _start;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec(v_x_1671_);
v___x_1683_ = lean_box(0);
v___x_1684_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_x_1669_, v___x_1683_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v_fst_1686_; lean_object* v_snd_1687_; lean_object* v_a_1689_; lean_object* v___y_1712_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v_fst_1686_ = lean_ctor_get(v_a_1685_, 0);
lean_inc(v_fst_1686_);
v_snd_1687_ = lean_ctor_get(v_a_1685_, 1);
lean_inc(v_snd_1687_);
lean_dec(v_a_1685_);
v___x_1722_ = lean_unsigned_to_nat(0u);
v___x_1723_ = lean_array_get_size(v_x_1670_);
v___x_1724_ = lean_nat_dec_lt(v___x_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_inc(v_snd_1687_);
v_a_1689_ = v_snd_1687_;
goto v___jp_1688_;
}
else
{
uint8_t v___x_1725_; 
v___x_1725_ = lean_nat_dec_le(v___x_1723_, v___x_1723_);
if (v___x_1725_ == 0)
{
if (v___x_1724_ == 0)
{
lean_inc(v_snd_1687_);
v_a_1689_ = v_snd_1687_;
goto v___jp_1688_;
}
else
{
size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = lean_usize_of_nat(v___x_1723_);
lean_inc(v_snd_1687_);
v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1670_, v___x_1726_, v___x_1727_, v_snd_1687_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
v___y_1712_ = v___x_1728_;
goto v___jp_1711_;
}
}
else
{
size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = lean_usize_of_nat(v___x_1723_);
lean_inc(v_snd_1687_);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__0(v_x_1670_, v___x_1729_, v___x_1730_, v_snd_1687_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
v___y_1712_ = v___x_1731_;
goto v___jp_1711_;
}
}
v___jp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1690_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_1667_, v_a_1689_, v___y_1673_);
lean_dec_ref(v___x_1690_);
v___x_1691_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___closed__0));
v___x_1692_ = l_Lean_mkAppN(v_fst_1686_, v_x_1670_);
lean_dec_ref(v_x_1670_);
v___x_1693_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_1691_, v_snd_1668_, v___x_1692_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___x_1693_, 0);
lean_dec(v_unused_1702_);
v___x_1695_ = v___x_1693_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v___x_1693_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = l_Lean_Expr_mvarId_x21(v_snd_1687_);
lean_dec(v_snd_1687_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v_snd_1687_);
v_a_1703_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1693_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1693_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
v___jp_1711_:
{
if (lean_obj_tag(v___y_1712_) == 0)
{
lean_object* v_a_1713_; 
v_a_1713_ = lean_ctor_get(v___y_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___y_1712_, 1);
v_a_1689_ = v_a_1713_;
goto v___jp_1688_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v_snd_1687_);
lean_dec(v_fst_1686_);
lean_dec_ref(v_x_1670_);
lean_dec_ref(v_snd_1668_);
lean_dec(v_mvarId_1667_);
v_a_1714_ = lean_ctor_get(v___y_1712_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___y_1712_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___y_1712_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___y_1712_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref(v_x_1670_);
lean_dec_ref(v_snd_1668_);
lean_dec(v_mvarId_1667_);
v_a_1732_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1684_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1684_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1667_ = stack[0].m_obj;
lean_object* v_snd_1668_ = stack[1].m_obj;
lean_object* v_x_1669_ = stack[2].m_obj;
lean_object* v_x_1670_ = stack[3].m_obj;
lean_object* v_x_1671_ = stack[4].m_obj;
lean_object* v___y_1672_ = stack[5].m_obj;
lean_object* v___y_1673_ = stack[6].m_obj;
lean_object* v___y_1674_ = stack[7].m_obj;
lean_object* v___y_1675_ = stack[8].m_obj;
lean_object* v_res_1740_;
v_res_1740_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1667_, v_snd_1668_, v_x_1669_, v_x_1670_, v_x_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
stack->m_obj
 = v_res_1740_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1___boxed(lean_object* v_mvarId_1741_, lean_object* v_snd_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1741_, v_snd_1742_, v_x_1743_, v_x_1744_, v_x_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1751_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__0));
v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
return v___x_1754_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(lean_object* v_mvarId_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
lean_inc(v_mvarId_1755_);
v___x_1761_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1797_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v_fst_1763_ = lean_ctor_get(v_a_1762_, 0);
v_snd_1764_ = lean_ctor_get(v_a_1762_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1766_ = v_a_1762_;
v_isShared_1767_ = v_isSharedCheck_1797_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_snd_1764_);
lean_inc(v_fst_1763_);
lean_dec(v_a_1762_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1797_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; uint8_t v___x_1782_; 
v___x_1768_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_1763_, v___y_1757_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_Expr_cleanupAnnotations(v_a_1769_);
v___x_1782_ = l_Lean_Expr_isApp(v___x_1770_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec(v_snd_1764_);
lean_dec(v_mvarId_1755_);
v___x_1783_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___closed__1);
v___x_1784_ = l_Lean_indentExpr(v___x_1770_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set_tag(v___x_1766_, 7);
lean_ctor_set(v___x_1766_, 1, v___x_1784_);
lean_ctor_set(v___x_1766_, 0, v___x_1783_);
v___x_1786_ = v___x_1766_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1787_; lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v___x_1787_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1786_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_del_object(v___x_1766_);
v___y_1772_ = v___y_1756_;
v___y_1773_ = v___y_1757_;
v___y_1774_ = v___y_1758_;
v___y_1775_ = v___y_1759_;
goto v___jp_1771_;
}
v___jp_1771_:
{
lean_object* v_dummy_1776_; lean_object* v_nargs_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v_dummy_1776_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_1777_ = l_Lean_Expr_getAppNumArgs(v___x_1770_);
lean_inc(v_nargs_1777_);
v___x_1778_ = lean_mk_array(v_nargs_1777_, v_dummy_1776_);
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_nat_sub(v_nargs_1777_, v___x_1779_);
lean_dec(v_nargs_1777_);
v___x_1781_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrFunN_spec__1(v_mvarId_1755_, v_snd_1764_, v___x_1770_, v___x_1778_, v___x_1780_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_mvarId_1755_);
v_a_1798_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1761_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1761_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congrFunN___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1755_ = stack[0].m_obj;
lean_object* v___y_1756_ = stack[1].m_obj;
lean_object* v___y_1757_ = stack[2].m_obj;
lean_object* v___y_1758_ = stack[3].m_obj;
lean_object* v___y_1759_ = stack[4].m_obj;
lean_object* v_res_1806_;
v_res_1806_ = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(v_mvarId_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
stack->m_obj
 = v_res_1806_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed(lean_object* v_mvarId_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Lean_Elab_Tactic_Conv_congrFunN___lam__0(v_mvarId_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
return v_res_1813_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congrFunN(lean_object* v_mvarId_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v___f_1820_; lean_object* v___x_1821_; 
lean_inc(v_mvarId_1814_);
v___f_1820_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrFunN___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1820_, 0, v_mvarId_1814_);
v___x_1821_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_1814_, v___f_1820_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
return v___x_1821_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congrFunN_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1814_ = stack[0].m_obj;
lean_object* v_a_1815_ = stack[1].m_obj;
lean_object* v_a_1816_ = stack[2].m_obj;
lean_object* v_a_1817_ = stack[3].m_obj;
lean_object* v_a_1818_ = stack[4].m_obj;
lean_object* v_res_1822_;
v_res_1822_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_mvarId_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
stack->m_obj
 = v_res_1822_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrFunN___boxed(lean_object* v_mvarId_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_mvarId_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(lean_object* v_msg_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = lean_panic_fn_borrowed(v___x_1831_, v_msg_1830_);
return v___x_1832_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1834_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_1835_ = lean_unsigned_to_nat(30u);
v___x_1836_ = lean_unsigned_to_nat(150u);
v___x_1837_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__0));
v___x_1838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_1839_ = l_mkPanicMessageWithDecl(v___x_1838_, v___x_1837_, v___x_1836_, v___x_1835_, v___x_1834_);
return v___x_1839_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(lean_object* v_fst_1840_, lean_object* v_snd_1841_, lean_object* v_fst_1842_, lean_object* v_fst_1843_, lean_object* v_00___1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___closed__1);
v___x_1851_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1(v___x_1850_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1862_; 
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1863_);
v___x_1853_ = v___x_1851_;
v_isShared_1854_ = v_isSharedCheck_1862_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v___x_1851_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1862_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v_fst_1840_);
lean_ctor_set(v___x_1855_, 1, v_snd_1841_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v_fst_1842_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_fst_1843_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1858_);
v___x_1860_ = v___x_1853_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_dec(v_fst_1843_);
lean_dec(v_fst_1842_);
lean_dec(v_snd_1841_);
lean_dec(v_fst_1840_);
v_a_1864_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1851_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1851_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1840_ = stack[0].m_obj;
lean_object* v_snd_1841_ = stack[1].m_obj;
lean_object* v_fst_1842_ = stack[2].m_obj;
lean_object* v_fst_1843_ = stack[3].m_obj;
lean_object* v_00___1844_ = stack[4].m_obj;
lean_object* v___y_1845_ = stack[5].m_obj;
lean_object* v___y_1846_ = stack[6].m_obj;
lean_object* v___y_1847_ = stack[7].m_obj;
lean_object* v___y_1848_ = stack[8].m_obj;
lean_object* v_res_1872_;
v_res_1872_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1840_, v_snd_1841_, v_fst_1842_, v_fst_1843_, v_00___1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
stack->m_obj
 = v_res_1872_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0___boxed(lean_object* v_fst_1873_, lean_object* v_snd_1874_, lean_object* v_fst_1875_, lean_object* v_fst_1876_, lean_object* v_00___1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1873_, v_snd_1874_, v_fst_1875_, v_fst_1876_, v_00___1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1883_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(lean_object* v_snd_1884_, lean_object* v_snd_1885_, lean_object* v___x_1886_, lean_object* v___x_1887_, lean_object* v_____r_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1894_ = l_Lean_Expr_mvarId_x21(v_snd_1884_);
v___x_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v_snd_1885_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1886_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1887_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1884_ = stack[0].m_obj;
lean_object* v_snd_1885_ = stack[1].m_obj;
lean_object* v___x_1886_ = stack[2].m_obj;
lean_object* v___x_1887_ = stack[3].m_obj;
lean_object* v_____r_1888_ = stack[4].m_obj;
lean_object* v___y_1889_ = stack[5].m_obj;
lean_object* v___y_1890_ = stack[6].m_obj;
lean_object* v___y_1891_ = stack[7].m_obj;
lean_object* v___y_1892_ = stack[8].m_obj;
lean_object* v_res_1901_;
v_res_1901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1884_, v_snd_1885_, v___x_1886_, v___x_1887_, v_____r_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
stack->m_obj
 = v_res_1901_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1___boxed(lean_object* v_snd_1902_, lean_object* v_snd_1903_, lean_object* v___x_1904_, lean_object* v___x_1905_, lean_object* v_____r_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1902_, v_snd_1903_, v___x_1904_, v___x_1905_, v_____r_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_snd_1902_);
return v_res_1912_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__0));
v___x_1915_ = l_Lean_stringToMessageData(v___x_1914_);
return v___x_1915_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(lean_object* v_upperBound_1916_, lean_object* v_args_1917_, lean_object* v___x_1918_, lean_object* v_origTag_1919_, lean_object* v_tacticName_1920_, lean_object* v_a_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_a_1929_; lean_object* v___y_1934_; uint8_t v___x_1953_; 
v___x_1953_ = lean_nat_dec_lt(v_a_1921_, v_upperBound_1916_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_b_1922_);
return v___x_1954_;
}
else
{
lean_object* v_snd_1955_; lean_object* v_snd_1956_; lean_object* v_fst_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2078_; 
v_snd_1955_ = lean_ctor_get(v_b_1922_, 1);
lean_inc(v_snd_1955_);
v_snd_1956_ = lean_ctor_get(v_snd_1955_, 1);
lean_inc(v_snd_1956_);
v_fst_1957_ = lean_ctor_get(v_b_1922_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_b_1922_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v_b_1922_, 1);
lean_dec(v_unused_2079_);
v___x_1959_ = v_b_1922_;
v_isShared_1960_ = v_isSharedCheck_2078_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_fst_1957_);
lean_dec(v_b_1922_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2078_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v_fst_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_2076_; 
v_fst_1961_ = lean_ctor_get(v_snd_1955_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_snd_1955_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_snd_1955_, 1);
lean_dec(v_unused_2077_);
v___x_1963_ = v_snd_1955_;
v_isShared_1964_ = v_isSharedCheck_2076_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_fst_1961_);
lean_dec(v_snd_1955_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_2076_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_fst_1965_; lean_object* v_snd_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2075_; 
v_fst_1965_ = lean_ctor_get(v_snd_1956_, 0);
v_snd_1966_ = lean_ctor_get(v_snd_1956_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_snd_1956_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_1968_ = v_snd_1956_;
v_isShared_1969_ = v_isSharedCheck_2075_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snd_1966_);
lean_inc(v_fst_1965_);
lean_dec(v_snd_1956_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2075_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1970_ = l_Lean_instInhabitedExpr;
v___x_1971_ = lean_array_get_borrowed(v___x_1970_, v_args_1917_, v_a_1921_);
v___x_1972_ = lean_array_fget_borrowed(v___x_1918_, v_a_1921_);
v___x_1973_ = lean_unbox(v___x_1972_);
switch(v___x_1973_)
{
case 1:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1968_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1959_);
v___x_1974_ = lean_box(0);
v___x_1975_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1965_, v_snd_1966_, v_fst_1961_, v_fst_1957_, v___x_1974_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
v___y_1934_ = v___x_1975_;
goto v___jp_1933_;
}
case 2:
{
lean_object* v___x_1976_; 
lean_del_object(v___x_1968_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1959_);
lean_inc(v_origTag_1919_);
lean_inc(v___x_1971_);
v___x_1976_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_1971_, v_origTag_1919_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2005_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v_fst_1978_ = lean_ctor_get(v_a_1977_, 0);
v_snd_1979_ = lean_ctor_get(v_a_1977_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1981_ = v_a_1977_;
v_isShared_1982_ = v_isSharedCheck_2005_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snd_1979_);
lean_inc(v_fst_1978_);
lean_dec(v_a_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2005_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_inc(v_fst_1978_);
v___x_1983_ = l_Lean_Expr_app___override(v_fst_1957_, v_fst_1978_);
lean_inc(v_snd_1979_);
lean_inc(v___x_1971_);
v___x_1984_ = l_Lean_mkApp3(v_fst_1961_, v___x_1971_, v_fst_1978_, v_snd_1979_);
if (lean_obj_tag(v_fst_1965_) == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_del_object(v___x_1981_);
v___x_1985_ = lean_box(0);
v___x_1986_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1979_, v_snd_1966_, v___x_1984_, v___x_1983_, v___x_1985_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v_snd_1979_);
v___y_1934_ = v___x_1986_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec_ref_known(v_fst_1965_, 1);
v___x_1987_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
lean_inc_ref(v_tacticName_1920_);
v___x_1988_ = l_Lean_stringToMessageData(v_tacticName_1920_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 7);
lean_ctor_set(v___x_1981_, 1, v___x_1988_);
lean_ctor_set(v___x_1981_, 0, v___x_1987_);
v___x_1990_ = v___x_1981_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_1992_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__1(v_snd_1979_, v_snd_1966_, v___x_1984_, v___x_1983_, v_a_1994_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v_snd_1979_);
v___y_1934_ = v___x_1995_;
goto v___jp_1933_;
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref(v___x_1984_);
lean_dec_ref(v___x_1983_);
lean_dec(v_snd_1979_);
lean_dec(v_snd_1966_);
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v_a_1996_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1993_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1993_);
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
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_dec(v_fst_1961_);
lean_dec(v_fst_1957_);
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v_a_2006_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1976_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1976_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
case 4:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_del_object(v___x_1968_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1959_);
v___x_2014_ = lean_box(0);
v___x_2015_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___lam__0(v_fst_1965_, v_snd_1966_, v_fst_1961_, v_fst_1957_, v___x_2014_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
v___y_1934_ = v___x_2015_;
goto v___jp_1933_;
}
case 5:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
lean_inc(v___x_1971_);
v___x_2016_ = l_Lean_Expr_app___override(v_fst_1961_, v___x_1971_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
lean_inc_ref(v___x_2016_);
v___x_2017_ = lean_infer_type(v___x_2016_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v___y_1924_);
lean_inc_ref(v___y_1923_);
v___x_2019_ = lean_whnf(v_a_2018_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l_Lean_Expr_bindingDomain_x21(v_a_2020_);
lean_dec(v_a_2020_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
v___x_2023_ = 0;
v___x_2024_ = lean_box(0);
v___x_2025_ = l_Lean_Meta_mkFreshExprMVar(v___x_2022_, v___x_2023_, v___x_2024_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_n(v_a_2026_, 3);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = l_Lean_Expr_app___override(v_fst_1957_, v_a_2026_);
v___x_2028_ = l_Lean_Expr_app___override(v___x_2016_, v_a_2026_);
v___x_2029_ = l_Lean_Expr_mvarId_x21(v_a_2026_);
lean_dec(v_a_2026_);
v___x_2030_ = lean_array_push(v_snd_1966_, v___x_2029_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v___x_2030_);
v___x_2032_ = v___x_1968_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_fst_1965_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2034_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___x_2032_);
lean_ctor_set(v___x_1963_, 0, v___x_2028_);
v___x_2034_ = v___x_1963_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2036_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_2034_);
lean_ctor_set(v___x_1959_, 0, v___x_2027_);
v___x_2036_ = v___x_1959_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
v_a_1929_ = v___x_2036_;
goto v___jp_1928_;
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref(v___x_2016_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1959_);
lean_dec(v_fst_1957_);
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v_a_2040_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2025_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2025_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v___x_2016_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1959_);
lean_dec(v_fst_1957_);
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v_a_2048_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2019_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2019_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v___x_2016_);
lean_del_object(v___x_1968_);
lean_dec(v_snd_1966_);
lean_dec(v_fst_1965_);
lean_del_object(v___x_1963_);
lean_del_object(v___x_1959_);
lean_dec(v_fst_1957_);
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v_a_2056_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2017_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2017_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
default: 
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
lean_inc_n(v___x_1971_, 2);
v___x_2064_ = l_Lean_Expr_app___override(v_fst_1957_, v___x_1971_);
v___x_2065_ = l_Lean_Expr_app___override(v_fst_1961_, v___x_1971_);
if (v_isShared_1969_ == 0)
{
v___x_2067_ = v___x_1968_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_fst_1965_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_snd_1966_);
v___x_2067_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2069_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___x_2067_);
lean_ctor_set(v___x_1963_, 0, v___x_2065_);
v___x_2069_ = v___x_1963_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_2069_);
lean_ctor_set(v___x_1959_, 0, v___x_2064_);
v___x_2071_ = v___x_1959_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
v_a_1929_ = v___x_2071_;
goto v___jp_1928_;
}
}
}
}
}
}
}
}
}
v___jp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_unsigned_to_nat(1u);
v___x_1931_ = lean_nat_add(v_a_1921_, v___x_1930_);
lean_dec(v_a_1921_);
v_a_1921_ = v___x_1931_;
v_b_1922_ = v_a_1929_;
goto _start;
}
v___jp_1933_:
{
if (lean_obj_tag(v___y_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1944_; 
v_a_1935_ = lean_ctor_get(v___y_1934_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___y_1934_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1937_ = v___y_1934_;
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___y_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1944_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
if (lean_obj_tag(v_a_1935_) == 0)
{
lean_object* v_a_1939_; lean_object* v___x_1941_; 
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v_a_1939_ = lean_ctor_get(v_a_1935_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v_a_1935_, 1);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v_a_1939_);
v___x_1941_ = v___x_1937_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
else
{
lean_object* v_a_1943_; 
lean_del_object(v___x_1937_);
v_a_1943_ = lean_ctor_get(v_a_1935_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v_a_1935_, 1);
v_a_1929_ = v_a_1943_;
goto v___jp_1928_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_a_1921_);
lean_dec_ref(v_tacticName_1920_);
lean_dec(v_origTag_1919_);
v_a_1945_ = lean_ctor_get(v___y_1934_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___y_1934_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___y_1934_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___y_1934_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1916_ = stack[0].m_obj;
lean_object* v_args_1917_ = stack[1].m_obj;
lean_object* v___x_1918_ = stack[2].m_obj;
lean_object* v_origTag_1919_ = stack[3].m_obj;
lean_object* v_tacticName_1920_ = stack[4].m_obj;
lean_object* v_a_1921_ = stack[5].m_obj;
lean_object* v_b_1922_ = stack[6].m_obj;
lean_object* v___y_1923_ = stack[7].m_obj;
lean_object* v___y_1924_ = stack[8].m_obj;
lean_object* v___y_1925_ = stack[9].m_obj;
lean_object* v___y_1926_ = stack[10].m_obj;
lean_object* v_res_2080_;
v_res_2080_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_1916_, v_args_1917_, v___x_1918_, v_origTag_1919_, v_tacticName_1920_, v_a_1921_, v_b_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
stack->m_obj
 = v_res_2080_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___boxed(lean_object* v_upperBound_2081_, lean_object* v_args_2082_, lean_object* v___x_2083_, lean_object* v_origTag_2084_, lean_object* v_tacticName_2085_, lean_object* v_a_2086_, lean_object* v_b_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2081_, v_args_2082_, v___x_2083_, v_origTag_2084_, v_tacticName_2085_, v_a_2086_, v_b_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___x_2083_);
lean_dec_ref(v_args_2082_);
lean_dec(v_upperBound_2081_);
return v_res_2093_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3(void){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__2));
v___x_2098_ = lean_unsigned_to_nat(14u);
v___x_2099_ = lean_unsigned_to_nat(22u);
v___x_2100_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__1));
v___x_2101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__0));
v___x_2102_ = l_mkPanicMessageWithDecl(v___x_2101_, v___x_2100_, v___x_2099_, v___x_2098_, v___x_2097_);
return v___x_2102_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__5));
v___x_2108_ = l_Lean_stringToMessageData(v___x_2107_);
return v___x_2108_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(lean_object* v_tacticName_2109_, lean_object* v_origTag_2110_, lean_object* v_f_2111_, lean_object* v_args_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v_lower_2133_; lean_object* v_upper_2134_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = 0;
v___x_2151_ = lean_array_get_size(v_args_2112_);
lean_inc_ref(v_f_2111_);
v___x_2152_ = l_Lean_Meta_getFunInfoNArgs(v_f_2111_, v___x_2151_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2154_ = l_Lean_Meta_getCongrSimpKindsForArgZero(v_a_2153_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = 0;
lean_inc_ref(v_f_2111_);
v___x_2157_ = l_Lean_Meta_mkCongrSimpCore_x3f(v_f_2111_, v_a_2153_, v_a_2155_, v___x_2156_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
if (lean_obj_tag(v_a_2158_) == 1)
{
lean_object* v_val_2159_; lean_object* v_proof_2160_; lean_object* v_argKinds_2161_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_val_2159_ = lean_ctor_get(v_a_2158_, 0);
lean_inc(v_val_2159_);
lean_dec_ref_known(v_a_2158_, 1);
v_proof_2160_ = lean_ctor_get(v_val_2159_, 1);
lean_inc_ref(v_proof_2160_);
v_argKinds_2161_ = lean_ctor_get(v_val_2159_, 2);
lean_inc_ref(v_argKinds_2161_);
lean_dec(v_val_2159_);
v___x_2188_ = lean_unsigned_to_nat(0u);
v___x_2189_ = lean_box(v___x_2150_);
v___x_2190_ = lean_array_get(v___x_2189_, v_argKinds_2161_, v___x_2188_);
lean_dec(v___x_2189_);
v___x_2191_ = lean_unbox(v___x_2190_);
lean_dec(v___x_2190_);
if (v___x_2191_ == 2)
{
v___y_2163_ = v_a_2113_;
v___y_2164_ = v_a_2114_;
v___y_2165_ = v_a_2115_;
v___y_2166_ = v_a_2116_;
goto v___jp_2162_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_argKinds_2161_);
lean_dec_ref(v_proof_2160_);
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_f_2111_);
lean_dec(v_origTag_2110_);
v___x_2192_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2193_ = l_Lean_stringToMessageData(v_tacticName_2109_);
v___x_2194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg___closed__1);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2196_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
v___jp_2162_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2167_ = lean_array_get_size(v_argKinds_2161_);
v___x_2168_ = lean_unsigned_to_nat(0u);
v___x_2169_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__4));
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_proof_2160_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_f_2111_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v___x_2167_, v_args_2112_, v_argKinds_2161_, v_origTag_2110_, v_tacticName_2109_, v___x_2168_, v___x_2171_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec_ref(v_argKinds_2161_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v_snd_2174_; lean_object* v_snd_2175_; lean_object* v_fst_2176_; lean_object* v_fst_2177_; lean_object* v_snd_2178_; uint8_t v___x_2179_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v_snd_2174_ = lean_ctor_get(v_a_2173_, 1);
lean_inc(v_snd_2174_);
lean_dec(v_a_2173_);
v_snd_2175_ = lean_ctor_get(v_snd_2174_, 1);
lean_inc(v_snd_2175_);
v_fst_2176_ = lean_ctor_get(v_snd_2174_, 0);
lean_inc(v_fst_2176_);
lean_dec(v_snd_2174_);
v_fst_2177_ = lean_ctor_get(v_snd_2175_, 0);
lean_inc(v_fst_2177_);
v_snd_2178_ = lean_ctor_get(v_snd_2175_, 1);
lean_inc(v_snd_2178_);
lean_dec(v_snd_2175_);
v___x_2179_ = lean_nat_dec_le(v___x_2167_, v___x_2168_);
if (v___x_2179_ == 0)
{
v___y_2126_ = v_snd_2178_;
v___y_2127_ = v_fst_2176_;
v___y_2128_ = v___y_2163_;
v___y_2129_ = v___y_2165_;
v___y_2130_ = v___y_2166_;
v___y_2131_ = v___y_2164_;
v___y_2132_ = v_fst_2177_;
v_lower_2133_ = v___x_2167_;
v_upper_2134_ = v___x_2151_;
goto v___jp_2125_;
}
else
{
v___y_2126_ = v_snd_2178_;
v___y_2127_ = v_fst_2176_;
v___y_2128_ = v___y_2163_;
v___y_2129_ = v___y_2165_;
v___y_2130_ = v___y_2166_;
v___y_2131_ = v___y_2164_;
v___y_2132_ = v_fst_2177_;
v_lower_2133_ = v___x_2168_;
v_upper_2134_ = v___x_2151_;
goto v___jp_2125_;
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_args_2112_);
v_a_2180_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2172_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2172_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_a_2158_);
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_f_2111_);
lean_dec(v_origTag_2110_);
v___x_2206_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2207_ = l_Lean_stringToMessageData(v_tacticName_2109_);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__6);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2208_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2210_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
return v___x_2211_;
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_f_2111_);
lean_dec(v_origTag_2110_);
lean_dec_ref(v_tacticName_2109_);
v_a_2212_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2157_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2157_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_a_2153_);
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_f_2111_);
lean_dec(v_origTag_2110_);
lean_dec_ref(v_tacticName_2109_);
v_a_2220_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2154_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2154_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
lean_dec_ref(v_args_2112_);
lean_dec_ref(v_f_2111_);
lean_dec(v_origTag_2110_);
lean_dec_ref(v_tacticName_2109_);
v_a_2228_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2152_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2152_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
v___jp_2118_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___y_2121_);
lean_ctor_set(v___x_2122_, 1, v___y_2119_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___y_2120_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
return v___x_2124_;
}
v___jp_2125_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = l_Array_toSubarray___redArg(v_args_2112_, v_lower_2133_, v_upper_2134_);
v___x_2136_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__0___redArg(v___x_2135_, v___y_2127_, v___y_2128_, v___y_2131_, v___y_2129_, v___y_2130_);
if (lean_obj_tag(v___x_2136_) == 0)
{
if (lean_obj_tag(v___y_2132_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___closed__3);
v___x_2139_ = l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__0(v___x_2138_);
v___y_2119_ = v___y_2126_;
v___y_2120_ = v_a_2137_;
v___y_2121_ = v___x_2139_;
goto v___jp_2118_;
}
else
{
lean_object* v_a_2140_; lean_object* v_val_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2136_, 1);
v_val_2141_ = lean_ctor_get(v___y_2132_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v___y_2132_, 1);
v___y_2119_ = v___y_2126_;
v___y_2120_ = v_a_2140_;
v___y_2121_ = v_val_2141_;
goto v___jp_2118_;
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v___y_2132_);
lean_dec(v___y_2126_);
v_a_2142_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2136_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2136_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_2109_ = stack[0].m_obj;
lean_object* v_origTag_2110_ = stack[1].m_obj;
lean_object* v_f_2111_ = stack[2].m_obj;
lean_object* v_args_2112_ = stack[3].m_obj;
lean_object* v_a_2113_ = stack[4].m_obj;
lean_object* v_a_2114_ = stack[5].m_obj;
lean_object* v_a_2115_ = stack[6].m_obj;
lean_object* v_a_2116_ = stack[7].m_obj;
lean_object* v_res_2236_;
v_res_2236_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_2109_, v_origTag_2110_, v_f_2111_, v_args_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
stack->m_obj
 = v_res_2236_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm___boxed(lean_object* v_tacticName_2237_, lean_object* v_origTag_2238_, lean_object* v_f_2239_, lean_object* v_args_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_2237_, v_origTag_2238_, v_f_2239_, v_args_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2246_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(lean_object* v_upperBound_2247_, lean_object* v_args_2248_, lean_object* v___x_2249_, lean_object* v_origTag_2250_, lean_object* v_tacticName_2251_, lean_object* v_inst_2252_, lean_object* v_R_2253_, lean_object* v_a_2254_, lean_object* v_b_2255_, lean_object* v_c_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___redArg(v_upperBound_2247_, v_args_2248_, v___x_2249_, v_origTag_2250_, v_tacticName_2251_, v_a_2254_, v_b_2255_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2247_ = stack[0].m_obj;
lean_object* v_args_2248_ = stack[1].m_obj;
lean_object* v___x_2249_ = stack[2].m_obj;
lean_object* v_origTag_2250_ = stack[3].m_obj;
lean_object* v_tacticName_2251_ = stack[4].m_obj;
lean_object* v_a_2254_ = stack[7].m_obj;
lean_object* v_b_2255_ = stack[8].m_obj;
lean_object* v___y_2257_ = stack[10].m_obj;
lean_object* v___y_2258_ = stack[11].m_obj;
lean_object* v___y_2259_ = stack[12].m_obj;
lean_object* v___y_2260_ = stack[13].m_obj;
lean_object* v_res_2263_;
v_res_2263_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(v_upperBound_2247_, v_args_2248_, v___x_2249_, v_origTag_2250_, v_tacticName_2251_, lean_box(0), lean_box(0), v_a_2254_, v_b_2255_, lean_box(0), v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
stack->m_obj
 = v_res_2263_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1___boxed(lean_object* v_upperBound_2264_, lean_object* v_args_2265_, lean_object* v___x_2266_, lean_object* v_origTag_2267_, lean_object* v_tacticName_2268_, lean_object* v_inst_2269_, lean_object* v_R_2270_, lean_object* v_a_2271_, lean_object* v_b_2272_, lean_object* v_c_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm_spec__1(v_upperBound_2264_, v_args_2265_, v___x_2266_, v_origTag_2267_, v_tacticName_2268_, v_inst_2269_, v_R_2270_, v_a_2271_, v_b_2272_, v_c_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v___x_2266_);
lean_dec_ref(v_args_2265_);
lean_dec(v_upperBound_2264_);
return v_res_2279_;
}
}
lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(lean_object* v_msg_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___f_2286_; lean_object* v___x_3702__overap_2287_; lean_object* v___x_2288_; 
v___f_2286_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__1___closed__0));
v___x_3702__overap_2287_ = lean_panic_fn_borrowed(v___f_2286_, v_msg_2280_);
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
v___x_2288_ = lean_apply_5(v___x_3702__overap_2287_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, lean_box(0));
return v___x_2288_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2280_ = stack[0].m_obj;
lean_object* v___y_2281_ = stack[1].m_obj;
lean_object* v___y_2282_ = stack[2].m_obj;
lean_object* v___y_2283_ = stack[3].m_obj;
lean_object* v___y_2284_ = stack[4].m_obj;
lean_object* v_res_2289_;
v_res_2289_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v_msg_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
stack->m_obj
 = v_res_2289_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1___boxed(lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v_msg_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2296_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(lean_object* v_binderType_2300_, lean_object* v_body_2301_, lean_object* v_mvarId_2302_, uint8_t v_domain_2303_, uint8_t v___x_2304_, lean_object* v_binderName_2305_, lean_object* v_tacticName_2306_, lean_object* v_rhs_2307_, lean_object* v_arg_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; 
lean_inc_ref(v_binderType_2300_);
v___x_2314_ = l_Lean_Meta_getLevel(v_binderType_2300_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = lean_expr_instantiate1(v_body_2301_, v_arg_2308_);
lean_inc(v_mvarId_2302_);
v___x_2317_ = l_Lean_MVarId_getTag(v_mvarId_2302_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
lean_inc_ref(v___x_2316_);
v___x_2319_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_2316_, v_a_2318_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v_fst_2321_; lean_object* v_snd_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2396_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v_fst_2321_ = lean_ctor_get(v_a_2320_, 0);
v_snd_2322_ = lean_ctor_get(v_a_2320_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_a_2320_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2324_ = v_a_2320_;
v_isShared_2325_ = v_isSharedCheck_2396_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snd_2322_);
lean_inc(v_fst_2321_);
lean_dec(v_a_2320_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2396_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_Meta_getLevel(v___x_2316_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_mk_empty_array_with_capacity(v___x_2328_);
v___x_2330_ = lean_array_push(v___x_2329_, v_arg_2308_);
v___x_2331_ = 1;
v___x_2332_ = l_Lean_Meta_mkLambdaFVars(v___x_2330_, v_fst_2321_, v_domain_2303_, v___x_2304_, v_domain_2303_, v___x_2304_, v___x_2331_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
lean_inc(v_snd_2322_);
v___x_2334_ = l_Lean_Meta_mkLambdaFVars(v___x_2330_, v_snd_2322_, v_domain_2303_, v___x_2304_, v_domain_2303_, v___x_2304_, v___x_2331_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec_ref(v___x_2330_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___closed__1));
v___x_2337_ = lean_box(0);
if (v_isShared_2325_ == 0)
{
lean_ctor_set_tag(v___x_2324_, 1);
lean_ctor_set(v___x_2324_, 1, v___x_2337_);
lean_ctor_set(v___x_2324_, 0, v_a_2327_);
v___x_2339_ = v___x_2324_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2327_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_a_2315_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_Expr_const___override(v___x_2336_, v___x_2340_);
v___x_2342_ = 0;
lean_inc_ref(v_binderType_2300_);
v___x_2343_ = l_Lean_Expr_lam___override(v_binderName_2305_, v_binderType_2300_, v_body_2301_, v___x_2342_);
v___x_2344_ = lean_unsigned_to_nat(4u);
v___x_2345_ = lean_mk_empty_array_with_capacity(v___x_2344_);
v___x_2346_ = lean_array_push(v___x_2345_, v_binderType_2300_);
v___x_2347_ = lean_array_push(v___x_2346_, v___x_2343_);
v___x_2348_ = lean_array_push(v___x_2347_, v_a_2333_);
v___x_2349_ = lean_array_push(v___x_2348_, v_a_2335_);
v___x_2350_ = l_Lean_mkAppN(v___x_2341_, v___x_2349_);
lean_dec_ref(v___x_2349_);
lean_inc_ref(v___x_2350_);
v___x_2351_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2306_, v_rhs_2307_, v___x_2350_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref_known(v___x_2351_, 1);
v___x_2352_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2302_, v___x_2350_, v___y_2310_);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v___x_2352_, 0);
lean_dec(v_unused_2362_);
v___x_2354_ = v___x_2352_;
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v___x_2352_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2361_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2356_ = l_Lean_Expr_mvarId_x21(v_snd_2322_);
lean_dec(v_snd_2322_);
v___x_2357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v___x_2337_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2357_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___x_2350_);
lean_dec(v_snd_2322_);
lean_dec(v_mvarId_2302_);
v_a_2363_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2351_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2351_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2333_);
lean_dec(v_a_2327_);
lean_del_object(v___x_2324_);
lean_dec(v_snd_2322_);
lean_dec(v_a_2315_);
lean_dec_ref(v_rhs_2307_);
lean_dec_ref(v_tacticName_2306_);
lean_dec(v_binderName_2305_);
lean_dec(v_mvarId_2302_);
lean_dec_ref(v_body_2301_);
lean_dec_ref(v_binderType_2300_);
v_a_2372_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2334_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2334_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v___x_2330_);
lean_dec(v_a_2327_);
lean_del_object(v___x_2324_);
lean_dec(v_snd_2322_);
lean_dec(v_a_2315_);
lean_dec_ref(v_rhs_2307_);
lean_dec_ref(v_tacticName_2306_);
lean_dec(v_binderName_2305_);
lean_dec(v_mvarId_2302_);
lean_dec_ref(v_body_2301_);
lean_dec_ref(v_binderType_2300_);
v_a_2380_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2332_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2332_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_del_object(v___x_2324_);
lean_dec(v_snd_2322_);
lean_dec(v_fst_2321_);
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2308_);
lean_dec_ref(v_rhs_2307_);
lean_dec_ref(v_tacticName_2306_);
lean_dec(v_binderName_2305_);
lean_dec(v_mvarId_2302_);
lean_dec_ref(v_body_2301_);
lean_dec_ref(v_binderType_2300_);
v_a_2388_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2326_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2326_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v___x_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2308_);
lean_dec_ref(v_rhs_2307_);
lean_dec_ref(v_tacticName_2306_);
lean_dec(v_binderName_2305_);
lean_dec(v_mvarId_2302_);
lean_dec_ref(v_body_2301_);
lean_dec_ref(v_binderType_2300_);
v_a_2397_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2319_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2319_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v___x_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_arg_2308_);
lean_dec_ref(v_rhs_2307_);
lean_dec_ref(v_tacticName_2306_);
lean_dec(v_binderName_2305_);
lean_dec(v_mvarId_2302_);
lean_dec_ref(v_body_2301_);
lean_dec_ref(v_binderType_2300_);
v_a_2405_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2317_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2317_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v_arg_2308_);
lean_dec_ref(v_rhs_2307_);
lean_dec_ref(v_tacticName_2306_);
lean_dec(v_binderName_2305_);
lean_dec(v_mvarId_2302_);
lean_dec_ref(v_body_2301_);
lean_dec_ref(v_binderType_2300_);
v_a_2413_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2314_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2314_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_binderType_2300_ = stack[0].m_obj;
lean_object* v_body_2301_ = stack[1].m_obj;
lean_object* v_mvarId_2302_ = stack[2].m_obj;
uint8_t v_domain_2303_ = stack[3].m_num;
uint8_t v___x_2304_ = stack[4].m_num;
lean_object* v_binderName_2305_ = stack[5].m_obj;
lean_object* v_tacticName_2306_ = stack[6].m_obj;
lean_object* v_rhs_2307_ = stack[7].m_obj;
lean_object* v_arg_2308_ = stack[8].m_obj;
lean_object* v___y_2309_ = stack[9].m_obj;
lean_object* v___y_2310_ = stack[10].m_obj;
lean_object* v___y_2311_ = stack[11].m_obj;
lean_object* v___y_2312_ = stack[12].m_obj;
lean_object* v_res_2421_;
v_res_2421_ = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(v_binderType_2300_, v_body_2301_, v_mvarId_2302_, v_domain_2303_, v___x_2304_, v_binderName_2305_, v_tacticName_2306_, v_rhs_2307_, v_arg_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
stack->m_obj
 = v_res_2421_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed(lean_object* v_binderType_2422_, lean_object* v_body_2423_, lean_object* v_mvarId_2424_, lean_object* v_domain_2425_, lean_object* v___x_2426_, lean_object* v_binderName_2427_, lean_object* v_tacticName_2428_, lean_object* v_rhs_2429_, lean_object* v_arg_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
uint8_t v_domain_boxed_2436_; uint8_t v___x_4141__boxed_2437_; lean_object* v_res_2438_; 
v_domain_boxed_2436_ = lean_unbox(v_domain_2425_);
v___x_4141__boxed_2437_ = lean_unbox(v___x_2426_);
v_res_2438_ = l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0(v_binderType_2422_, v_body_2423_, v_mvarId_2424_, v_domain_boxed_2436_, v___x_4141__boxed_2437_, v_binderName_2427_, v_tacticName_2428_, v_rhs_2429_, v_arg_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
return v_res_2438_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2439_, lean_object* v_b_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; 
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
v___x_2446_ = lean_apply_6(v_k_2439_, v_b_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, lean_box(0));
return v___x_2446_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2439_ = stack[0].m_obj;
lean_object* v_b_2440_ = stack[1].m_obj;
lean_object* v___y_2441_ = stack[2].m_obj;
lean_object* v___y_2442_ = stack[3].m_obj;
lean_object* v___y_2443_ = stack[4].m_obj;
lean_object* v___y_2444_ = stack[5].m_obj;
lean_object* v_res_2447_;
v_res_2447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(v_k_2439_, v_b_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
stack->m_obj
 = v_res_2447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2448_, lean_object* v_b_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0(v_k_2448_, v_b_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v_res_2455_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(lean_object* v_name_2456_, uint8_t v_bi_2457_, lean_object* v_type_2458_, lean_object* v_k_2459_, uint8_t v_kind_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___f_2466_; lean_object* v___x_2467_; 
v___f_2466_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2466_, 0, v_k_2459_);
v___x_2467_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2456_, v_bi_2457_, v_type_2458_, v___f_2466_, v_kind_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2467_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2467_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2456_ = stack[0].m_obj;
uint8_t v_bi_2457_ = stack[1].m_num;
lean_object* v_type_2458_ = stack[2].m_obj;
lean_object* v_k_2459_ = stack[3].m_obj;
uint8_t v_kind_2460_ = stack[4].m_num;
lean_object* v___y_2461_ = stack[5].m_obj;
lean_object* v___y_2462_ = stack[6].m_obj;
lean_object* v___y_2463_ = stack[7].m_obj;
lean_object* v___y_2464_ = stack[8].m_obj;
lean_object* v_res_2484_;
v_res_2484_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2456_, v_bi_2457_, v_type_2458_, v_k_2459_, v_kind_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
stack->m_obj
 = v_res_2484_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg___boxed(lean_object* v_name_2485_, lean_object* v_bi_2486_, lean_object* v_type_2487_, lean_object* v_k_2488_, lean_object* v_kind_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v_bi_boxed_2495_; uint8_t v_kind_boxed_2496_; lean_object* v_res_2497_; 
v_bi_boxed_2495_ = lean_unbox(v_bi_2486_);
v_kind_boxed_2496_ = lean_unbox(v_kind_2489_);
v_res_2497_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2485_, v_bi_boxed_2495_, v_type_2487_, v_k_2488_, v_kind_boxed_2496_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2497_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(lean_object* v_name_2498_, lean_object* v_type_2499_, lean_object* v_k_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = 0;
v___x_2507_ = 0;
v___x_2508_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2498_, v___x_2506_, v_type_2499_, v_k_2500_, v___x_2507_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2508_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2498_ = stack[0].m_obj;
lean_object* v_type_2499_ = stack[1].m_obj;
lean_object* v_k_2500_ = stack[2].m_obj;
lean_object* v___y_2501_ = stack[3].m_obj;
lean_object* v___y_2502_ = stack[4].m_obj;
lean_object* v___y_2503_ = stack[5].m_obj;
lean_object* v___y_2504_ = stack[6].m_obj;
lean_object* v_res_2509_;
v_res_2509_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2498_, v_type_2499_, v_k_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
stack->m_obj
 = v_res_2509_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg___boxed(lean_object* v_name_2510_, lean_object* v_type_2511_, lean_object* v_k_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2510_, v_type_2511_, v_k_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
return v_res_2518_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__0));
v___x_2521_ = l_Lean_stringToMessageData(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2526_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__2));
v___x_2527_ = lean_unsigned_to_nat(33u);
v___x_2528_ = lean_unsigned_to_nat(158u);
v___x_2529_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__4));
v___x_2530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrThm_spec__2___redArg___lam__0___closed__0));
v___x_2531_ = l_mkPanicMessageWithDecl(v___x_2530_, v___x_2529_, v___x_2528_, v___x_2527_, v___x_2526_);
return v___x_2531_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall(lean_object* v_tacticName_2532_, uint8_t v_domain_2533_, lean_object* v_mvarId_2534_, lean_object* v_lhs_2535_, lean_object* v_rhs_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
if (lean_obj_tag(v_lhs_2535_) == 7)
{
lean_object* v_binderName_2542_; lean_object* v_binderType_2543_; lean_object* v_body_2544_; uint8_t v_binderInfo_2545_; lean_object* v___y_2547_; 
v_binderName_2542_ = lean_ctor_get(v_lhs_2535_, 0);
lean_inc(v_binderName_2542_);
v_binderType_2543_ = lean_ctor_get(v_lhs_2535_, 1);
lean_inc_ref(v_binderType_2543_);
v_body_2544_ = lean_ctor_get(v_lhs_2535_, 2);
lean_inc_ref(v_body_2544_);
v_binderInfo_2545_ = lean_ctor_get_uint8(v_lhs_2535_, sizeof(void*)*3 + 8);
if (v_domain_2533_ == 0)
{
uint8_t v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___f_2633_; lean_object* v___x_2634_; 
lean_dec_ref_known(v_lhs_2535_, 3);
v___x_2630_ = 1;
v___x_2631_ = lean_box(v_domain_2533_);
v___x_2632_ = lean_box(v___x_2630_);
lean_inc(v_binderName_2542_);
lean_inc_ref(v_binderType_2543_);
v___f_2633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgForall___lam__0___boxed), 14, 8);
lean_closure_set(v___f_2633_, 0, v_binderType_2543_);
lean_closure_set(v___f_2633_, 1, v_body_2544_);
lean_closure_set(v___f_2633_, 2, v_mvarId_2534_);
lean_closure_set(v___f_2633_, 3, v___x_2631_);
lean_closure_set(v___f_2633_, 4, v___x_2632_);
lean_closure_set(v___f_2633_, 5, v_binderName_2542_);
lean_closure_set(v___f_2633_, 6, v_tacticName_2532_);
lean_closure_set(v___f_2633_, 7, v_rhs_2536_);
v___x_2634_ = l_Lean_Core_mkFreshUserName(v_binderName_2542_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_a_2635_, v_binderType_2543_, v___f_2633_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
return v___x_2636_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v___f_2633_);
lean_dec_ref(v_binderType_2543_);
v_a_2637_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2634_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2634_);
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
uint8_t v___x_2645_; 
v___x_2645_ = l_Lean_Expr_hasLooseBVars(v_body_2544_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_dec_ref_known(v_lhs_2535_, 3);
lean_inc(v_mvarId_2534_);
v___x_2646_ = l_Lean_MVarId_getTag(v_mvarId_2534_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2543_, v_a_2647_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_fst_2650_; lean_object* v_snd_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2704_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v_fst_2650_ = lean_ctor_get(v_a_2649_, 0);
v_snd_2651_ = lean_ctor_get(v_a_2649_, 1);
v_isSharedCheck_2704_ = !lean_is_exclusive(v_a_2649_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2653_ = v_a_2649_;
v_isShared_2654_ = v_isSharedCheck_2704_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_snd_2651_);
lean_inc(v_fst_2650_);
lean_dec(v_a_2649_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2704_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; 
lean_inc_ref(v_body_2544_);
v___x_2655_ = l_Lean_Meta_mkEqRefl(v_body_2544_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__3));
v___x_2658_ = lean_unsigned_to_nat(2u);
v___x_2659_ = lean_mk_empty_array_with_capacity(v___x_2658_);
lean_inc(v_snd_2651_);
v___x_2660_ = lean_array_push(v___x_2659_, v_snd_2651_);
v___x_2661_ = lean_array_push(v___x_2660_, v_a_2656_);
v___x_2662_ = l_Lean_Meta_mkAppM(v___x_2657_, v___x_2661_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2664_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2534_, v_a_2663_, v_a_2538_);
lean_dec_ref(v___x_2664_);
v___x_2665_ = l_Lean_Expr_forallE___override(v_binderName_2542_, v_fst_2650_, v_body_2544_, v_binderInfo_2545_);
v___x_2666_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v_tacticName_2532_, v_rhs_2536_, v___x_2665_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2678_; 
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; 
v_unused_2679_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2679_);
v___x_2668_ = v___x_2666_;
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v___x_2666_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = l_Lean_Expr_mvarId_x21(v_snd_2651_);
lean_dec(v_snd_2651_);
v___x_2671_ = lean_box(0);
if (v_isShared_2654_ == 0)
{
lean_ctor_set_tag(v___x_2653_, 1);
lean_ctor_set(v___x_2653_, 1, v___x_2671_);
lean_ctor_set(v___x_2653_, 0, v___x_2670_);
v___x_2673_ = v___x_2653_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2675_ = v___x_2668_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_del_object(v___x_2653_);
lean_dec(v_snd_2651_);
v_a_2680_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2666_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2666_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_del_object(v___x_2653_);
lean_dec(v_snd_2651_);
lean_dec(v_fst_2650_);
lean_dec_ref(v_body_2544_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2688_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2662_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2662_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_del_object(v___x_2653_);
lean_dec(v_snd_2651_);
lean_dec(v_fst_2650_);
lean_dec_ref(v_body_2544_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2696_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2655_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2655_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
else
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2712_; 
lean_dec_ref(v_body_2544_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2705_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2707_ = v___x_2648_;
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2648_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2712_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_a_2705_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref(v_body_2544_);
lean_dec_ref(v_binderType_2543_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2713_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2646_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2646_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
else
{
lean_object* v___x_2721_; 
lean_inc_ref(v_body_2544_);
v___x_2721_ = l_Lean_Meta_isProp(v_body_2544_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; uint8_t v___x_2723_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v___x_2723_ = lean_unbox(v_a_2722_);
if (v___x_2723_ == 0)
{
lean_dec_ref_known(v_lhs_2535_, 3);
v___y_2547_ = v___x_2721_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2724_; 
lean_dec_ref_known(v___x_2721_, 1);
v___x_2724_ = l_Lean_Meta_isProp(v_lhs_2535_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
v___y_2547_ = v___x_2724_;
goto v___jp_2546_;
}
}
else
{
lean_dec_ref_known(v_lhs_2535_, 3);
v___y_2547_ = v___x_2721_;
goto v___jp_2546_;
}
}
}
v___jp_2546_:
{
if (lean_obj_tag(v___y_2547_) == 0)
{
lean_object* v_a_2548_; uint8_t v___x_2549_; 
v_a_2548_ = lean_ctor_get(v___y_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___y_2547_, 1);
v___x_2549_ = lean_unbox(v_a_2548_);
lean_dec(v_a_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec_ref(v_body_2544_);
lean_dec_ref(v_binderType_2543_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
v___x_2550_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof___closed__3);
v___x_2551_ = l_Lean_stringToMessageData(v_tacticName_2532_);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__1);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2554_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; 
lean_inc(v_mvarId_2534_);
v___x_2556_ = l_Lean_MVarId_getTag(v_mvarId_2534_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
lean_inc_ref(v_binderType_2543_);
v___x_2558_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_binderType_2543_, v_a_2557_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2604_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v_snd_2560_ = lean_ctor_get(v_a_2559_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_a_2559_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v_a_2559_, 0);
lean_dec(v_unused_2605_);
v___x_2562_ = v_a_2559_;
v_isShared_2563_ = v_isSharedCheck_2604_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_dec(v_a_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2604_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2564_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgForall___closed__3));
v___x_2565_ = 0;
v___x_2566_ = l_Lean_Expr_lam___override(v_binderName_2542_, v_binderType_2543_, v_body_2544_, v___x_2565_);
v___x_2567_ = lean_unsigned_to_nat(2u);
v___x_2568_ = lean_mk_empty_array_with_capacity(v___x_2567_);
lean_inc(v_snd_2560_);
v___x_2569_ = lean_array_push(v___x_2568_, v_snd_2560_);
v___x_2570_ = lean_array_push(v___x_2569_, v___x_2566_);
v___x_2571_ = l_Lean_Meta_mkAppM(v___x_2564_, v___x_2570_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc_n(v_a_2572_, 2);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_2532_, v_rhs_2536_, v_a_2572_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref_known(v___x_2573_, 1);
v___x_2574_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_2534_, v_a_2572_, v_a_2538_);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v___x_2574_, 0);
lean_dec(v_unused_2587_);
v___x_2576_ = v___x_2574_;
v_isShared_2577_ = v_isSharedCheck_2586_;
goto v_resetjp_2575_;
}
else
{
lean_dec(v___x_2574_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2586_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2578_ = l_Lean_Expr_mvarId_x21(v_snd_2560_);
lean_dec(v_snd_2560_);
v___x_2579_ = lean_box(0);
if (v_isShared_2563_ == 0)
{
lean_ctor_set_tag(v___x_2562_, 1);
lean_ctor_set(v___x_2562_, 1, v___x_2579_);
lean_ctor_set(v___x_2562_, 0, v___x_2578_);
v___x_2581_ = v___x_2562_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2583_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2581_);
v___x_2583_ = v___x_2576_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_a_2572_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec(v_mvarId_2534_);
v_a_2588_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2573_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2573_);
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
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2596_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2571_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2571_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v_body_2544_);
lean_dec_ref(v_binderType_2543_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2606_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2558_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2558_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v_body_2544_);
lean_dec_ref(v_binderType_2543_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2614_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2556_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2556_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec_ref(v_body_2544_);
lean_dec_ref(v_binderType_2543_);
lean_dec(v_binderName_2542_);
lean_dec_ref(v_rhs_2536_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v_a_2622_ = lean_ctor_get(v___y_2547_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___y_2547_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___y_2547_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___y_2547_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec_ref(v_rhs_2536_);
lean_dec_ref(v_lhs_2535_);
lean_dec(v_mvarId_2534_);
lean_dec_ref(v_tacticName_2532_);
v___x_2725_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgForall___closed__5);
v___x_2726_ = l_panic___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__1(v___x_2725_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
return v___x_2726_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congrArgForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_2532_ = stack[0].m_obj;
uint8_t v_domain_2533_ = stack[1].m_num;
lean_object* v_mvarId_2534_ = stack[2].m_obj;
lean_object* v_lhs_2535_ = stack[3].m_obj;
lean_object* v_rhs_2536_ = stack[4].m_obj;
lean_object* v_a_2537_ = stack[5].m_obj;
lean_object* v_a_2538_ = stack[6].m_obj;
lean_object* v_a_2539_ = stack[7].m_obj;
lean_object* v_a_2540_ = stack[8].m_obj;
lean_object* v_res_2727_;
v_res_2727_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_2532_, v_domain_2533_, v_mvarId_2534_, v_lhs_2535_, v_rhs_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
stack->m_obj
 = v_res_2727_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgForall___boxed(lean_object* v_tacticName_2728_, lean_object* v_domain_2729_, lean_object* v_mvarId_2730_, lean_object* v_lhs_2731_, lean_object* v_rhs_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
uint8_t v_domain_boxed_2738_; lean_object* v_res_2739_; 
v_domain_boxed_2738_ = lean_unbox(v_domain_2729_);
v_res_2739_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_2728_, v_domain_boxed_2738_, v_mvarId_2730_, v_lhs_2731_, v_rhs_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2739_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_object* v_00_u03b1_2740_, lean_object* v_name_2741_, uint8_t v_bi_2742_, lean_object* v_type_2743_, lean_object* v_k_2744_, uint8_t v_kind_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___redArg(v_name_2741_, v_bi_2742_, v_type_2743_, v_k_2744_, v_kind_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2741_ = stack[1].m_obj;
uint8_t v_bi_2742_ = stack[2].m_num;
lean_object* v_type_2743_ = stack[3].m_obj;
lean_object* v_k_2744_ = stack[4].m_obj;
uint8_t v_kind_2745_ = stack[5].m_num;
lean_object* v___y_2746_ = stack[6].m_obj;
lean_object* v___y_2747_ = stack[7].m_obj;
lean_object* v___y_2748_ = stack[8].m_obj;
lean_object* v___y_2749_ = stack[9].m_obj;
lean_object* v_res_2752_;
v_res_2752_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(lean_box(0), v_name_2741_, v_bi_2742_, v_type_2743_, v_k_2744_, v_kind_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
stack->m_obj
 = v_res_2752_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2753_, lean_object* v_name_2754_, lean_object* v_bi_2755_, lean_object* v_type_2756_, lean_object* v_k_2757_, lean_object* v_kind_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v_bi_boxed_2764_; uint8_t v_kind_boxed_2765_; lean_object* v_res_2766_; 
v_bi_boxed_2764_ = lean_unbox(v_bi_2755_);
v_kind_boxed_2765_ = lean_unbox(v_kind_2758_);
v_res_2766_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0(v_00_u03b1_2753_, v_name_2754_, v_bi_boxed_2764_, v_type_2756_, v_k_2757_, v_kind_boxed_2765_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
return v_res_2766_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_object* v_00_u03b1_2767_, lean_object* v_name_2768_, lean_object* v_type_2769_, lean_object* v_k_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_name_2768_, v_type_2769_, v_k_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2768_ = stack[1].m_obj;
lean_object* v_type_2769_ = stack[2].m_obj;
lean_object* v_k_2770_ = stack[3].m_obj;
lean_object* v___y_2771_ = stack[4].m_obj;
lean_object* v___y_2772_ = stack[5].m_obj;
lean_object* v___y_2773_ = stack[6].m_obj;
lean_object* v___y_2774_ = stack[7].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(lean_box(0), v_name_2768_, v_type_2769_, v_k_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_name_2779_, lean_object* v_type_2780_, lean_object* v_k_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0(v_00_u03b1_2778_, v_name_2779_, v_type_2780_, v_k_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__0(lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_nat_to_int(v_a_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__0));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(lean_object* v_snd_2793_, lean_object* v_a_2794_, lean_object* v_____r_2795_, lean_object* v_fType_2796_, lean_object* v_j_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
if (lean_obj_tag(v_fType_2796_) == 7)
{
lean_object* v_body_2803_; uint8_t v_binderInfo_2804_; uint8_t v___x_2805_; 
v_body_2803_ = lean_ctor_get(v_fType_2796_, 2);
lean_inc_ref(v_body_2803_);
v_binderInfo_2804_ = lean_ctor_get_uint8(v_fType_2796_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_fType_2796_, 3);
v___x_2805_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_dec(v_a_2794_);
lean_inc(v_j_2797_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_j_2797_);
lean_ctor_set(v___x_2806_, 1, v_snd_2793_);
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v_body_2803_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
return v___x_2809_;
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2810_ = lean_array_push(v_snd_2793_, v_a_2794_);
lean_inc(v_j_2797_);
v___x_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2811_, 0, v_j_2797_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v_body_2803_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
lean_dec(v_a_2794_);
v___x_2815_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___closed__1);
v___x_2816_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_2815_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2826_; 
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2816_, 0);
lean_dec(v_unused_2827_);
v___x_2818_ = v___x_2816_;
v_isShared_2819_ = v_isSharedCheck_2826_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v___x_2816_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2826_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
lean_inc(v_j_2797_);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_j_2797_);
lean_ctor_set(v___x_2820_, 1, v_snd_2793_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_fType_2796_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2822_);
v___x_2824_ = v___x_2818_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v_fType_2796_);
lean_dec(v_snd_2793_);
v_a_2828_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2816_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2816_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2793_ = stack[0].m_obj;
lean_object* v_a_2794_ = stack[1].m_obj;
lean_object* v_____r_2795_ = stack[2].m_obj;
lean_object* v_fType_2796_ = stack[3].m_obj;
lean_object* v_j_2797_ = stack[4].m_obj;
lean_object* v___y_2798_ = stack[5].m_obj;
lean_object* v___y_2799_ = stack[6].m_obj;
lean_object* v___y_2800_ = stack[7].m_obj;
lean_object* v___y_2801_ = stack[8].m_obj;
lean_object* v_res_2836_;
v_res_2836_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2793_, v_a_2794_, v_____r_2795_, v_fType_2796_, v_j_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
stack->m_obj
 = v_res_2836_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0___boxed(lean_object* v_snd_2837_, lean_object* v_a_2838_, lean_object* v_____r_2839_, lean_object* v_fType_2840_, lean_object* v_j_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2837_, v_a_2838_, v_____r_2839_, v_fType_2840_, v_j_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v_j_2841_);
return v_res_2847_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(lean_object* v_upperBound_2848_, lean_object* v_xs_2849_, lean_object* v_a_2850_, lean_object* v_b_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___y_2858_; uint8_t v___x_2880_; 
v___x_2880_ = lean_nat_dec_lt(v_a_2850_, v_upperBound_2848_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; 
lean_dec(v_a_2850_);
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v_b_2851_);
return v___x_2881_;
}
else
{
lean_object* v_snd_2882_; lean_object* v_fst_2883_; lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___y_2887_; uint8_t v___x_2899_; 
v_snd_2882_ = lean_ctor_get(v_b_2851_, 1);
lean_inc(v_snd_2882_);
v_fst_2883_ = lean_ctor_get(v_b_2851_, 0);
lean_inc(v_fst_2883_);
lean_dec_ref(v_b_2851_);
v_fst_2884_ = lean_ctor_get(v_snd_2882_, 0);
lean_inc(v_fst_2884_);
v_snd_2885_ = lean_ctor_get(v_snd_2882_, 1);
lean_inc(v_snd_2885_);
lean_dec(v_snd_2882_);
v___x_2899_ = l_Lean_Expr_isForall(v_fst_2883_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; uint8_t v_transparency_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2900_ = l_Lean_Meta_Context_config(v___y_2852_);
v_transparency_2901_ = lean_ctor_get_uint8(v___x_2900_, 9);
lean_dec_ref(v___x_2900_);
v___x_2902_ = 0;
v___x_2903_ = lean_expr_instantiate_rev_range(v_fst_2883_, v_fst_2884_, v_a_2850_, v_xs_2849_);
lean_dec(v_fst_2884_);
lean_dec(v_fst_2883_);
v___x_2904_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2901_, v___x_2902_);
if (v___x_2904_ == 0)
{
lean_object* v_keyedConfig_2905_; uint8_t v_trackZetaDelta_2906_; lean_object* v_zetaDeltaSet_2907_; lean_object* v_lctx_2908_; lean_object* v_localInstances_2909_; lean_object* v_defEqCtx_x3f_2910_; lean_object* v_synthPendingDepth_2911_; lean_object* v_customCanUnfoldPredicate_x3f_2912_; uint8_t v_univApprox_2913_; uint8_t v_inTypeClassResolution_2914_; uint8_t v_cacheInferType_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_keyedConfig_2905_ = lean_ctor_get(v___y_2852_, 0);
v_trackZetaDelta_2906_ = lean_ctor_get_uint8(v___y_2852_, sizeof(void*)*7);
v_zetaDeltaSet_2907_ = lean_ctor_get(v___y_2852_, 1);
v_lctx_2908_ = lean_ctor_get(v___y_2852_, 2);
v_localInstances_2909_ = lean_ctor_get(v___y_2852_, 3);
v_defEqCtx_x3f_2910_ = lean_ctor_get(v___y_2852_, 4);
v_synthPendingDepth_2911_ = lean_ctor_get(v___y_2852_, 5);
v_customCanUnfoldPredicate_x3f_2912_ = lean_ctor_get(v___y_2852_, 6);
v_univApprox_2913_ = lean_ctor_get_uint8(v___y_2852_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2914_ = lean_ctor_get_uint8(v___y_2852_, sizeof(void*)*7 + 2);
v_cacheInferType_2915_ = lean_ctor_get_uint8(v___y_2852_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2905_);
v___x_2916_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2902_, v_keyedConfig_2905_);
lean_inc(v_customCanUnfoldPredicate_x3f_2912_);
lean_inc(v_synthPendingDepth_2911_);
lean_inc(v_defEqCtx_x3f_2910_);
lean_inc_ref(v_localInstances_2909_);
lean_inc_ref(v_lctx_2908_);
lean_inc(v_zetaDeltaSet_2907_);
v___x_2917_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v_zetaDeltaSet_2907_);
lean_ctor_set(v___x_2917_, 2, v_lctx_2908_);
lean_ctor_set(v___x_2917_, 3, v_localInstances_2909_);
lean_ctor_set(v___x_2917_, 4, v_defEqCtx_x3f_2910_);
lean_ctor_set(v___x_2917_, 5, v_synthPendingDepth_2911_);
lean_ctor_set(v___x_2917_, 6, v_customCanUnfoldPredicate_x3f_2912_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*7, v_trackZetaDelta_2906_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*7 + 1, v_univApprox_2913_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2914_);
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*7 + 3, v_cacheInferType_2915_);
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
v___x_2918_ = lean_whnf(v___x_2903_, v___x_2917_, v___y_2853_, v___y_2854_, v___y_2855_);
v___y_2887_ = v___x_2918_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2919_; 
lean_inc(v___y_2855_);
lean_inc_ref(v___y_2854_);
lean_inc(v___y_2853_);
lean_inc_ref(v___y_2852_);
v___x_2919_ = lean_whnf(v___x_2903_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
v___y_2887_ = v___x_2919_;
goto v___jp_2886_;
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_box(0);
lean_inc(v_a_2850_);
v___x_2921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2885_, v_a_2850_, v___x_2920_, v_fst_2883_, v_fst_2884_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v_fst_2884_);
v___y_2858_ = v___x_2921_;
goto v___jp_2857_;
}
v___jp_2886_:
{
if (lean_obj_tag(v___y_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v_a_2888_ = lean_ctor_get(v___y_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___y_2887_, 1);
v___x_2889_ = lean_box(0);
lean_inc(v_a_2850_);
v___x_2890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___lam__0(v_snd_2885_, v_a_2850_, v___x_2889_, v_a_2888_, v_a_2850_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
v___y_2858_ = v___x_2890_;
goto v___jp_2857_;
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_snd_2885_);
lean_dec(v_a_2850_);
v_a_2891_ = lean_ctor_get(v___y_2887_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___y_2887_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___y_2887_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___y_2887_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
v___jp_2857_:
{
if (lean_obj_tag(v___y_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2871_; 
v_a_2859_ = lean_ctor_get(v___y_2858_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___y_2858_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2861_ = v___y_2858_;
v_isShared_2862_ = v_isSharedCheck_2871_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___y_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2871_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
if (lean_obj_tag(v_a_2859_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; 
lean_dec(v_a_2850_);
v_a_2863_ = lean_ctor_get(v_a_2859_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v_a_2859_, 1);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v_a_2863_);
v___x_2865_ = v___x_2861_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_del_object(v___x_2861_);
v_a_2867_ = lean_ctor_get(v_a_2859_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v_a_2859_, 1);
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_add(v_a_2850_, v___x_2868_);
lean_dec(v_a_2850_);
v_a_2850_ = v___x_2869_;
v_b_2851_ = v_a_2867_;
goto _start;
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2850_);
v_a_2872_ = lean_ctor_get(v___y_2858_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___y_2858_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___y_2858_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___y_2858_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2848_ = stack[0].m_obj;
lean_object* v_xs_2849_ = stack[1].m_obj;
lean_object* v_a_2850_ = stack[2].m_obj;
lean_object* v_b_2851_ = stack[3].m_obj;
lean_object* v___y_2852_ = stack[4].m_obj;
lean_object* v___y_2853_ = stack[5].m_obj;
lean_object* v___y_2854_ = stack[6].m_obj;
lean_object* v___y_2855_ = stack[7].m_obj;
lean_object* v_res_2922_;
v_res_2922_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_2848_, v_xs_2849_, v_a_2850_, v_b_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
stack->m_obj
 = v_res_2922_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg___boxed(lean_object* v_upperBound_2923_, lean_object* v_xs_2924_, lean_object* v_a_2925_, lean_object* v_b_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_2923_, v_xs_2924_, v_a_2925_, v_b_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_xs_2924_);
lean_dec(v_upperBound_2923_);
return v_res_2932_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__2));
v___x_2940_ = l_Lean_stringToMessageData(v___x_2939_);
return v___x_2940_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__4));
v___x_2943_ = l_Lean_stringToMessageData(v___x_2942_);
return v___x_2943_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_unsigned_to_nat(0u);
v___x_2945_ = lean_nat_to_int(v___x_2944_);
return v___x_2945_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = lean_unsigned_to_nat(1u);
v___x_2947_ = lean_nat_to_int(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__8));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(lean_object* v_tacticName_2951_, uint8_t v_explicit_2952_, lean_object* v_f_2953_, lean_object* v_xs_2954_, lean_object* v_i_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_){
_start:
{
lean_object* v___y_2962_; lean_object* v_lower_2963_; lean_object* v_upper_2964_; lean_object* v___y_2970_; lean_object* v_lower_2971_; lean_object* v_upper_2972_; 
if (v_explicit_2952_ == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_2959_);
lean_inc_ref(v_a_2958_);
lean_inc(v_a_2957_);
lean_inc_ref(v_a_2956_);
lean_inc_ref(v_f_2953_);
v___x_2978_ = lean_infer_type(v_f_2953_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = lean_array_get_size(v_xs_2954_);
v___x_2981_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__1));
v___x_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2982_, 0, v_a_2979_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
v___x_2983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v___x_2980_, v_xs_2954_, v___x_2977_, v___x_2982_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v_snd_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3043_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v_snd_2985_ = lean_ctor_get(v_a_2984_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v_a_2984_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; 
v_unused_3044_ = lean_ctor_get(v_a_2984_, 0);
lean_dec(v_unused_3044_);
v___x_2987_ = v_a_2984_;
v_isShared_2988_ = v_isSharedCheck_3043_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_snd_2985_);
lean_dec(v_a_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3043_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_snd_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3041_; 
v_snd_2989_ = lean_ctor_get(v_snd_2985_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_snd_2985_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_snd_2985_, 0);
lean_dec(v_unused_3042_);
v___x_2991_ = v_snd_2985_;
v_isShared_2992_ = v_isSharedCheck_3041_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_snd_2989_);
lean_dec(v_snd_2985_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3041_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___y_2994_; lean_object* v___y_3002_; lean_object* v___x_3028_; lean_object* v___y_3030_; uint8_t v___x_3035_; 
v___x_3028_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3035_ = lean_int_dec_lt(v___x_3028_, v_i_2955_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = lean_array_get_size(v_snd_2989_);
v___x_3037_ = lean_nat_to_int(v___x_3036_);
v___x_3038_ = lean_int_add(v_i_2955_, v___x_3037_);
lean_dec(v___x_3037_);
v___y_3030_ = v___x_3038_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3040_ = lean_int_sub(v_i_2955_, v___x_3039_);
v___y_3030_ = v___x_3040_;
goto v___jp_3029_;
}
v___jp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2995_ = lean_nat_abs(v___y_2994_);
lean_dec(v___y_2994_);
v___x_2996_ = lean_array_get(v___x_2977_, v_snd_2989_, v___x_2995_);
lean_dec(v___x_2995_);
lean_dec(v_snd_2989_);
lean_inc(v___x_2996_);
lean_inc_ref(v_xs_2954_);
v___x_2997_ = l_Array_toSubarray___redArg(v_xs_2954_, v___x_2977_, v___x_2996_);
v___x_2998_ = l_Subarray_copy___redArg(v___x_2997_);
v___x_2999_ = l_Lean_mkAppN(v_f_2953_, v___x_2998_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = lean_nat_dec_le(v___x_2996_, v___x_2977_);
if (v___x_3000_ == 0)
{
v___y_2970_ = v___x_2999_;
v_lower_2971_ = v___x_2996_;
v_upper_2972_ = v___x_2980_;
goto v___jp_2969_;
}
else
{
lean_dec(v___x_2996_);
v___y_2970_ = v___x_2999_;
v_lower_2971_ = v___x_2977_;
v_upper_2972_ = v___x_2980_;
goto v___jp_2969_;
}
}
v___jp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
lean_dec(v___y_3002_);
v___x_3003_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3004_ = l_Lean_stringToMessageData(v_tacticName_2951_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 7);
lean_ctor_set(v___x_2991_, 1, v___x_3004_);
lean_ctor_set(v___x_2991_, 0, v___x_3003_);
v___x_3006_ = v___x_2991_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3009_; 
v___x_3007_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 7);
lean_ctor_set(v___x_2987_, 1, v___x_3007_);
lean_ctor_set(v___x_2987_, 0, v___x_3006_);
v___x_3009_ = v___x_2987_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v___x_3007_);
v___x_3009_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v___x_3010_ = lean_array_get_size(v_snd_2989_);
lean_dec(v_snd_2989_);
v___x_3011_ = l_Nat_reprFast(v___x_3010_);
v___x_3012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
v___x_3013_ = l_Lean_MessageData_ofFormat(v___x_3012_);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3009_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__5);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3016_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
v___jp_3029_:
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_int_dec_lt(v___y_3030_, v___x_3028_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3032_ = lean_array_get_size(v_snd_2989_);
v___x_3033_ = lean_nat_to_int(v___x_3032_);
v___x_3034_ = lean_int_dec_le(v___x_3033_, v___y_3030_);
lean_dec(v___x_3033_);
if (v___x_3034_ == 0)
{
lean_del_object(v___x_2991_);
lean_del_object(v___x_2987_);
lean_dec_ref(v_tacticName_2951_);
v___y_2994_ = v___y_3030_;
goto v___jp_2993_;
}
else
{
lean_dec_ref(v_xs_2954_);
lean_dec_ref(v_f_2953_);
v___y_3002_ = v___y_3030_;
goto v___jp_3001_;
}
}
else
{
lean_dec_ref(v_xs_2954_);
lean_dec_ref(v_f_2953_);
v___y_3002_ = v___y_3030_;
goto v___jp_3001_;
}
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref(v_xs_2954_);
lean_dec_ref(v_f_2953_);
lean_dec_ref(v_tacticName_2951_);
v_a_3045_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2983_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2983_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v_xs_2954_);
lean_dec_ref(v_f_2953_);
lean_dec_ref(v_tacticName_2951_);
v_a_3053_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2978_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2978_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v___x_3061_; lean_object* v___y_3063_; lean_object* v___y_3071_; lean_object* v___x_3093_; lean_object* v___y_3095_; uint8_t v___x_3100_; 
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3093_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3100_ = lean_int_dec_lt(v___x_3093_, v_i_2955_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_array_get_size(v_xs_2954_);
v___x_3102_ = lean_nat_to_int(v___x_3101_);
v___x_3103_ = lean_int_add(v_i_2955_, v___x_3102_);
lean_dec(v___x_3102_);
v___y_3095_ = v___x_3103_;
goto v___jp_3094_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3104_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3105_ = lean_int_sub(v_i_2955_, v___x_3104_);
v___y_3095_ = v___x_3105_;
goto v___jp_3094_;
}
v___jp_3062_:
{
lean_object* v_idx_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___x_3069_; 
v_idx_3064_ = lean_nat_abs(v___y_3063_);
lean_dec(v___y_3063_);
lean_inc(v_idx_3064_);
lean_inc_ref(v_xs_2954_);
v___x_3065_ = l_Array_toSubarray___redArg(v_xs_2954_, v___x_3061_, v_idx_3064_);
v___x_3066_ = l_Subarray_copy___redArg(v___x_3065_);
v___x_3067_ = l_Lean_mkAppN(v_f_2953_, v___x_3066_);
lean_dec_ref(v___x_3066_);
v___x_3068_ = lean_array_get_size(v_xs_2954_);
v___x_3069_ = lean_nat_dec_le(v_idx_3064_, v___x_3061_);
if (v___x_3069_ == 0)
{
v___y_2962_ = v___x_3067_;
v_lower_2963_ = v_idx_3064_;
v_upper_2964_ = v___x_3068_;
goto v___jp_2961_;
}
else
{
lean_dec(v_idx_3064_);
v___y_2962_ = v___x_3067_;
v_lower_2963_ = v___x_3061_;
v_upper_2964_ = v___x_3068_;
goto v___jp_2961_;
}
}
v___jp_3070_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v___y_3071_);
v___x_3072_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3073_ = l_Lean_stringToMessageData(v_tacticName_2951_);
v___x_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3072_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__3);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_array_get_size(v_xs_2954_);
lean_dec_ref(v_xs_2954_);
v___x_3078_ = l_Nat_reprFast(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3078_);
v___x_3080_ = l_Lean_MessageData_ofFormat(v___x_3079_);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3076_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__9);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3083_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
v___jp_3094_:
{
uint8_t v___x_3096_; 
v___x_3096_ = lean_int_dec_lt(v___y_3095_, v___x_3093_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3097_ = lean_array_get_size(v_xs_2954_);
v___x_3098_ = lean_nat_to_int(v___x_3097_);
v___x_3099_ = lean_int_dec_le(v___x_3098_, v___y_3095_);
lean_dec(v___x_3098_);
if (v___x_3099_ == 0)
{
lean_dec_ref(v_tacticName_2951_);
v___y_3063_ = v___y_3095_;
goto v___jp_3062_;
}
else
{
lean_dec_ref(v_f_2953_);
v___y_3071_ = v___y_3095_;
goto v___jp_3070_;
}
}
else
{
lean_dec_ref(v_f_2953_);
v___y_3071_ = v___y_3095_;
goto v___jp_3070_;
}
}
}
v___jp_2961_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2965_ = l_Array_toSubarray___redArg(v_xs_2954_, v_lower_2963_, v_upper_2964_);
v___x_2966_ = l_Subarray_copy___redArg(v___x_2965_);
v___x_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___y_2962_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
return v___x_2968_;
}
v___jp_2969_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2973_ = l_Array_toSubarray___redArg(v_xs_2954_, v_lower_2971_, v_upper_2972_);
v___x_2974_ = l_Subarray_copy___redArg(v___x_2973_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___y_2970_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
return v___x_2976_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_2951_ = stack[0].m_obj;
uint8_t v_explicit_2952_ = stack[1].m_num;
lean_object* v_f_2953_ = stack[2].m_obj;
lean_object* v_xs_2954_ = stack[3].m_obj;
lean_object* v_i_2955_ = stack[4].m_obj;
lean_object* v_a_2956_ = stack[5].m_obj;
lean_object* v_a_2957_ = stack[6].m_obj;
lean_object* v_a_2958_ = stack[7].m_obj;
lean_object* v_a_2959_ = stack[8].m_obj;
lean_object* v_res_3106_;
v_res_3106_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_2951_, v_explicit_2952_, v_f_2953_, v_xs_2954_, v_i_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
stack->m_obj
 = v_res_3106_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___boxed(lean_object* v_tacticName_3107_, lean_object* v_explicit_3108_, lean_object* v_f_3109_, lean_object* v_xs_3110_, lean_object* v_i_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
uint8_t v_explicit_boxed_3117_; lean_object* v_res_3118_; 
v_explicit_boxed_3117_ = lean_unbox(v_explicit_3108_);
v_res_3118_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3107_, v_explicit_boxed_3117_, v_f_3109_, v_xs_3110_, v_i_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_);
lean_dec(v_a_3115_);
lean_dec_ref(v_a_3114_);
lean_dec(v_a_3113_);
lean_dec_ref(v_a_3112_);
lean_dec(v_i_3111_);
return v_res_3118_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(lean_object* v_upperBound_3119_, lean_object* v_xs_3120_, lean_object* v_inst_3121_, lean_object* v_R_3122_, lean_object* v_a_3123_, lean_object* v_b_3124_, lean_object* v_c_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___redArg(v_upperBound_3119_, v_xs_3120_, v_a_3123_, v_b_3124_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3119_ = stack[0].m_obj;
lean_object* v_xs_3120_ = stack[1].m_obj;
lean_object* v_a_3123_ = stack[4].m_obj;
lean_object* v_b_3124_ = stack[5].m_obj;
lean_object* v___y_3126_ = stack[7].m_obj;
lean_object* v___y_3127_ = stack[8].m_obj;
lean_object* v___y_3128_ = stack[9].m_obj;
lean_object* v___y_3129_ = stack[10].m_obj;
lean_object* v_res_3132_;
v_res_3132_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(v_upperBound_3119_, v_xs_3120_, lean_box(0), lean_box(0), v_a_3123_, v_b_3124_, lean_box(0), v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
stack->m_obj
 = v_res_3132_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1___boxed(lean_object* v_upperBound_3133_, lean_object* v_xs_3134_, lean_object* v_inst_3135_, lean_object* v_R_3136_, lean_object* v_a_3137_, lean_object* v_b_3138_, lean_object* v_c_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v_res_3145_; 
v_res_3145_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs_spec__1(v_upperBound_3133_, v_xs_3134_, v_inst_3135_, v_R_3136_, v_a_3137_, v_b_3138_, v_c_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v_xs_3134_);
lean_dec(v_upperBound_3133_);
return v_res_3145_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(lean_object* v_tacticName_3146_, uint8_t v_explicit_3147_, lean_object* v_i_3148_, lean_object* v_mvarId_3149_, lean_object* v_snd_3150_, lean_object* v_x_3151_, lean_object* v_x_3152_, lean_object* v_x_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
if (lean_obj_tag(v_x_3151_) == 5)
{
lean_object* v_fn_3159_; lean_object* v_arg_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_fn_3159_ = lean_ctor_get(v_x_3151_, 0);
lean_inc_ref(v_fn_3159_);
v_arg_3160_ = lean_ctor_get(v_x_3151_, 1);
lean_inc_ref(v_arg_3160_);
lean_dec_ref_known(v_x_3151_, 2);
v___x_3161_ = lean_array_set(v_x_3152_, v_x_3153_, v_arg_3160_);
v___x_3162_ = lean_unsigned_to_nat(1u);
v___x_3163_ = lean_nat_sub(v_x_3153_, v___x_3162_);
lean_dec(v_x_3153_);
v_x_3151_ = v_fn_3159_;
v_x_3152_ = v___x_3161_;
v_x_3153_ = v___x_3163_;
goto _start;
}
else
{
lean_object* v___x_3165_; 
lean_dec(v_x_3153_);
lean_inc_ref(v_tacticName_3146_);
v___x_3165_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs(v_tacticName_3146_, v_explicit_3147_, v_x_3151_, v_x_3152_, v_i_3148_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v_fst_3167_; lean_object* v_snd_3168_; lean_object* v___x_3169_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v_fst_3167_ = lean_ctor_get(v_a_3166_, 0);
lean_inc(v_fst_3167_);
v_snd_3168_ = lean_ctor_get(v_a_3166_, 1);
lean_inc(v_snd_3168_);
lean_dec(v_a_3166_);
lean_inc(v_mvarId_3149_);
v___x_3169_ = l_Lean_MVarId_getTag(v_mvarId_3149_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3169_, 1);
lean_inc_ref(v_tacticName_3146_);
v___x_3171_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_mkCongrArgZeroThm(v_tacticName_3146_, v_a_3170_, v_fst_3167_, v_snd_3168_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v_snd_3173_; lean_object* v_fst_3174_; lean_object* v_fst_3175_; lean_object* v_snd_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3202_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3171_, 1);
v_snd_3173_ = lean_ctor_get(v_a_3172_, 1);
lean_inc(v_snd_3173_);
v_fst_3174_ = lean_ctor_get(v_a_3172_, 0);
lean_inc(v_fst_3174_);
lean_dec(v_a_3172_);
v_fst_3175_ = lean_ctor_get(v_snd_3173_, 0);
v_snd_3176_ = lean_ctor_get(v_snd_3173_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_snd_3173_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3178_ = v_snd_3173_;
v_isShared_3179_ = v_isSharedCheck_3202_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_snd_3176_);
lean_inc(v_fst_3175_);
lean_dec(v_snd_3173_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3202_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; 
lean_inc(v_fst_3174_);
v___x_3180_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhsFromProof(v_tacticName_3146_, v_snd_3150_, v_fst_3174_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref_known(v___x_3180_, 1);
v___x_3181_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_3149_, v_fst_3174_, v___y_3155_);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v___x_3181_, 0);
lean_dec(v_unused_3193_);
v___x_3183_ = v___x_3181_;
v_isShared_3184_ = v_isSharedCheck_3192_;
goto v_resetjp_3182_;
}
else
{
lean_dec(v___x_3181_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3192_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = lean_array_to_list(v_snd_3176_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set_tag(v___x_3178_, 1);
lean_ctor_set(v___x_3178_, 1, v___x_3185_);
v___x_3187_ = v___x_3178_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_fst_3175_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
lean_object* v___x_3189_; 
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3187_);
v___x_3189_ = v___x_3183_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_del_object(v___x_3178_);
lean_dec(v_snd_3176_);
lean_dec(v_fst_3175_);
lean_dec(v_fst_3174_);
lean_dec(v_mvarId_3149_);
v_a_3194_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3180_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3180_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref(v_snd_3150_);
lean_dec(v_mvarId_3149_);
lean_dec_ref(v_tacticName_3146_);
v_a_3203_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3171_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3171_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_snd_3168_);
lean_dec(v_fst_3167_);
lean_dec_ref(v_snd_3150_);
lean_dec(v_mvarId_3149_);
lean_dec_ref(v_tacticName_3146_);
v_a_3211_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3169_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3169_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v_snd_3150_);
lean_dec(v_mvarId_3149_);
lean_dec_ref(v_tacticName_3146_);
v_a_3219_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3165_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3165_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_3146_ = stack[0].m_obj;
uint8_t v_explicit_3147_ = stack[1].m_num;
lean_object* v_i_3148_ = stack[2].m_obj;
lean_object* v_mvarId_3149_ = stack[3].m_obj;
lean_object* v_snd_3150_ = stack[4].m_obj;
lean_object* v_x_3151_ = stack[5].m_obj;
lean_object* v_x_3152_ = stack[6].m_obj;
lean_object* v_x_3153_ = stack[7].m_obj;
lean_object* v___y_3154_ = stack[8].m_obj;
lean_object* v___y_3155_ = stack[9].m_obj;
lean_object* v___y_3156_ = stack[10].m_obj;
lean_object* v___y_3157_ = stack[11].m_obj;
lean_object* v_res_3227_;
v_res_3227_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3146_, v_explicit_3147_, v_i_3148_, v_mvarId_3149_, v_snd_3150_, v_x_3151_, v_x_3152_, v_x_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
stack->m_obj
 = v_res_3227_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0___boxed(lean_object* v_tacticName_3228_, lean_object* v_explicit_3229_, lean_object* v_i_3230_, lean_object* v_mvarId_3231_, lean_object* v_snd_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_, lean_object* v_x_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
uint8_t v_explicit_boxed_3241_; lean_object* v_res_3242_; 
v_explicit_boxed_3241_ = lean_unbox(v_explicit_3229_);
v_res_3242_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3228_, v_explicit_boxed_3241_, v_i_3230_, v_mvarId_3231_, v_snd_3232_, v_x_3233_, v_x_3234_, v_x_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v_i_3230_);
return v_res_3242_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_unsigned_to_nat(2u);
v___x_3244_ = lean_nat_to_int(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3246_ = lean_int_neg(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__2));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__4));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(lean_object* v_mvarId_3253_, lean_object* v_tacticName_3254_, uint8_t v_explicit_3255_, lean_object* v_i_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v___x_3262_; 
lean_inc(v_mvarId_3253_);
v___x_3262_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_3253_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v_fst_3264_; lean_object* v_snd_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3324_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v_fst_3264_ = lean_ctor_get(v_a_3263_, 0);
v_snd_3265_ = lean_ctor_get(v_a_3263_, 1);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_a_3263_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3267_ = v_a_3263_;
v_isShared_3268_ = v_isSharedCheck_3324_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snd_3265_);
lean_inc(v_fst_3264_);
lean_dec(v_a_3263_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3324_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3302_; 
v___x_3269_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_3264_, v___y_3258_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
v___x_3271_ = l_Lean_Expr_cleanupAnnotations(v_a_3270_);
v___x_3272_ = l_Lean_Expr_isForall(v___x_3271_);
if (v___x_3272_ == 0)
{
uint8_t v___x_3305_; 
lean_del_object(v___x_3267_);
v___x_3305_ = l_Lean_Expr_isApp(v___x_3271_);
if (v___x_3305_ == 0)
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec(v_snd_3265_);
lean_dec(v_mvarId_3253_);
v___x_3306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3307_ = l_Lean_stringToMessageData(v_tacticName_3254_);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__5);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = l_Lean_indentExpr(v___x_3271_);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3312_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
return v___x_3313_;
}
else
{
lean_object* v_dummy_3314_; lean_object* v_nargs_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v_dummy_3314_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_congr___lam__0___closed__2);
v_nargs_3315_ = l_Lean_Expr_getAppNumArgs(v___x_3271_);
lean_inc(v_nargs_3315_);
v___x_3316_ = lean_mk_array(v_nargs_3315_, v_dummy_3314_);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_nat_sub(v_nargs_3315_, v___x_3317_);
lean_dec(v_nargs_3315_);
v___x_3319_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Conv_congrArgN_spec__0(v_tacticName_3254_, v_explicit_3255_, v_i_3256_, v_mvarId_3253_, v_snd_3265_, v___x_3271_, v___x_3316_, v___x_3318_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
return v___x_3319_;
}
}
else
{
lean_object* v___x_3320_; uint8_t v___x_3321_; 
v___x_3320_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3321_ = lean_int_dec_lt(v_i_3256_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3323_ = lean_int_dec_eq(v_i_3256_, v___x_3322_);
v___y_3302_ = v___x_3323_;
goto v___jp_3301_;
}
else
{
v___y_3302_ = v___x_3272_;
goto v___jp_3301_;
}
}
v___jp_3273_:
{
lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3278_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3279_ = lean_int_dec_eq(v_i_3256_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3281_ = lean_int_dec_eq(v_i_3256_, v___x_3280_);
v___x_3282_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3254_, v___x_3281_, v_mvarId_3253_, v___x_3271_, v_snd_3265_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Elab_Tactic_Conv_congrArgForall(v_tacticName_3254_, v___x_3272_, v_mvarId_3253_, v___x_3271_, v_snd_3265_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
return v___x_3283_;
}
}
v___jp_3284_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3288_; 
v___x_3285_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs___closed__1);
v___x_3286_ = l_Lean_stringToMessageData(v_tacticName_3254_);
if (v_isShared_3268_ == 0)
{
lean_ctor_set_tag(v___x_3267_, 7);
lean_ctor_set(v___x_3267_, 1, v___x_3286_);
lean_ctor_set(v___x_3267_, 0, v___x_3285_);
v___x_3288_ = v___x_3267_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v___x_3286_);
v___x_3288_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v___x_3289_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__3);
v___x_3290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3288_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_3290_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3291_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
v___jp_3301_:
{
if (v___y_3302_ == 0)
{
lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__0);
v___x_3304_ = lean_int_dec_lt(v___x_3303_, v_i_3256_);
if (v___x_3304_ == 0)
{
lean_del_object(v___x_3267_);
v___y_3274_ = v___y_3257_;
v___y_3275_ = v___y_3258_;
v___y_3276_ = v___y_3259_;
v___y_3277_ = v___y_3260_;
goto v___jp_3273_;
}
else
{
lean_dec_ref(v___x_3271_);
lean_dec(v_snd_3265_);
lean_dec(v_mvarId_3253_);
goto v___jp_3284_;
}
}
else
{
lean_dec_ref(v___x_3271_);
lean_dec(v_snd_3265_);
lean_dec(v_mvarId_3253_);
goto v___jp_3284_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref(v_tacticName_3254_);
lean_dec(v_mvarId_3253_);
v_a_3325_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3262_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3262_);
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
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congrArgN___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3253_ = stack[0].m_obj;
lean_object* v_tacticName_3254_ = stack[1].m_obj;
uint8_t v_explicit_3255_ = stack[2].m_num;
lean_object* v_i_3256_ = stack[3].m_obj;
lean_object* v___y_3257_ = stack[4].m_obj;
lean_object* v___y_3258_ = stack[5].m_obj;
lean_object* v___y_3259_ = stack[6].m_obj;
lean_object* v___y_3260_ = stack[7].m_obj;
lean_object* v_res_3333_;
v_res_3333_ = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(v_mvarId_3253_, v_tacticName_3254_, v_explicit_3255_, v_i_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
stack->m_obj
 = v_res_3333_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed(lean_object* v_mvarId_3334_, lean_object* v_tacticName_3335_, lean_object* v_explicit_3336_, lean_object* v_i_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
uint8_t v_explicit_boxed_3343_; lean_object* v_res_3344_; 
v_explicit_boxed_3343_ = lean_unbox(v_explicit_3336_);
v_res_3344_ = l_Lean_Elab_Tactic_Conv_congrArgN___lam__0(v_mvarId_3334_, v_tacticName_3335_, v_explicit_boxed_3343_, v_i_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v_i_3337_);
return v_res_3344_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_congrArgN(lean_object* v_tacticName_3345_, lean_object* v_mvarId_3346_, lean_object* v_i_3347_, uint8_t v_explicit_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v___x_3354_; lean_object* v___f_3355_; lean_object* v___x_3356_; 
v___x_3354_ = lean_box(v_explicit_3348_);
lean_inc(v_mvarId_3346_);
v___f_3355_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___boxed), 9, 4);
lean_closure_set(v___f_3355_, 0, v_mvarId_3346_);
lean_closure_set(v___f_3355_, 1, v_tacticName_3345_);
lean_closure_set(v___f_3355_, 2, v___x_3354_);
lean_closure_set(v___f_3355_, 3, v_i_3347_);
v___x_3356_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_3346_, v___f_3355_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
return v___x_3356_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_congrArgN_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_3345_ = stack[0].m_obj;
lean_object* v_mvarId_3346_ = stack[1].m_obj;
lean_object* v_i_3347_ = stack[2].m_obj;
uint8_t v_explicit_3348_ = stack[3].m_num;
lean_object* v_a_3349_ = stack[4].m_obj;
lean_object* v_a_3350_ = stack[5].m_obj;
lean_object* v_a_3351_ = stack[6].m_obj;
lean_object* v_a_3352_ = stack[7].m_obj;
lean_object* v_res_3357_;
v_res_3357_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3345_, v_mvarId_3346_, v_i_3347_, v_explicit_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_);
stack->m_obj
 = v_res_3357_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_congrArgN___boxed(lean_object* v_tacticName_3358_, lean_object* v_mvarId_3359_, lean_object* v_i_3360_, lean_object* v_explicit_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_){
_start:
{
uint8_t v_explicit_boxed_3367_; lean_object* v_res_3368_; 
v_explicit_boxed_3367_ = lean_unbox(v_explicit_3361_);
v_res_3368_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3358_, v_mvarId_3359_, v_i_3360_, v_explicit_boxed_3367_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3368_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg(lean_object* v_tacticName_3369_, lean_object* v_i_3370_, uint8_t v_explicit_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__6);
v___x_3379_ = lean_int_dec_eq(v_i_3370_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; 
v___x_3380_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
v___x_3382_ = l_Lean_Elab_Tactic_Conv_congrArgN(v_tacticName_3369_, v_a_3381_, v_i_3370_, v_explicit_3371_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
v___x_3384_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_3383_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
return v___x_3384_;
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
v_a_3385_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3382_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3382_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec(v_i_3370_);
lean_dec_ref(v_tacticName_3369_);
v_a_3393_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3380_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3380_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v___x_3401_; 
lean_dec(v_i_3370_);
lean_dec_ref(v_tacticName_3369_);
v___x_3401_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3403_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v___x_3403_ = l_Lean_Elab_Tactic_Conv_congrFunN(v_a_3402_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v_a_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_a_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3403_, 1);
v___x_3405_ = lean_box(0);
v___x_3406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3406_, 0, v_a_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_3406_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
return v___x_3407_;
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
v_a_3408_ = lean_ctor_get(v___x_3403_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3403_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3403_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3403_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
v_a_3416_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3401_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3401_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_3369_ = stack[0].m_obj;
lean_object* v_i_3370_ = stack[1].m_obj;
uint8_t v_explicit_3371_ = stack[2].m_num;
lean_object* v_a_3372_ = stack[3].m_obj;
lean_object* v_a_3373_ = stack[4].m_obj;
lean_object* v_a_3374_ = stack[5].m_obj;
lean_object* v_a_3375_ = stack[6].m_obj;
lean_object* v_a_3376_ = stack[7].m_obj;
lean_object* v_res_3424_;
v_res_3424_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3369_, v_i_3370_, v_explicit_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_);
stack->m_obj
 = v_res_3424_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___redArg___boxed(lean_object* v_tacticName_3425_, lean_object* v_i_3426_, lean_object* v_explicit_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_){
_start:
{
uint8_t v_explicit_boxed_3434_; lean_object* v_res_3435_; 
v_explicit_boxed_3434_ = lean_unbox(v_explicit_3427_);
v_res_3435_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3425_, v_i_3426_, v_explicit_boxed_3434_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_a_3430_);
lean_dec_ref(v_a_3429_);
lean_dec(v_a_3428_);
return v_res_3435_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalArg(lean_object* v_tacticName_3436_, lean_object* v_i_3437_, uint8_t v_explicit_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v_tacticName_3436_, v_i_3437_, v_explicit_3438_, v_a_3440_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
return v___x_3448_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tacticName_3436_ = stack[0].m_obj;
lean_object* v_i_3437_ = stack[1].m_obj;
uint8_t v_explicit_3438_ = stack[2].m_num;
lean_object* v_a_3439_ = stack[3].m_obj;
lean_object* v_a_3440_ = stack[4].m_obj;
lean_object* v_a_3441_ = stack[5].m_obj;
lean_object* v_a_3442_ = stack[6].m_obj;
lean_object* v_a_3443_ = stack[7].m_obj;
lean_object* v_a_3444_ = stack[8].m_obj;
lean_object* v_a_3445_ = stack[9].m_obj;
lean_object* v_a_3446_ = stack[10].m_obj;
lean_object* v_res_3449_;
v_res_3449_ = l_Lean_Elab_Tactic_Conv_evalArg(v_tacticName_3436_, v_i_3437_, v_explicit_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
stack->m_obj
 = v_res_3449_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalArg___boxed(lean_object* v_tacticName_3450_, lean_object* v_i_3451_, lean_object* v_explicit_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
uint8_t v_explicit_boxed_3462_; lean_object* v_res_3463_; 
v_explicit_boxed_3462_ = lean_unbox(v_explicit_3452_);
v_res_3463_ = l_Lean_Elab_Tactic_Conv_evalArg(v_tacticName_3450_, v_i_3451_, v_explicit_boxed_3462_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
return v_res_3463_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = lean_box(0);
v___x_3465_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_3464_);
return v___x_3466_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg(){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___closed__0);
v___x_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3470_;
v_res_3470_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
stack->m_obj
 = v_res_3470_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg___boxed(lean_object* v___y_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v_res_3472_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_object* v_00_u03b1_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3483_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3474_ = stack[1].m_obj;
lean_object* v___y_3475_ = stack[2].m_obj;
lean_object* v___y_3476_ = stack[3].m_obj;
lean_object* v___y_3477_ = stack[4].m_obj;
lean_object* v___y_3478_ = stack[5].m_obj;
lean_object* v___y_3479_ = stack[6].m_obj;
lean_object* v___y_3480_ = stack[7].m_obj;
lean_object* v___y_3481_ = stack[8].m_obj;
lean_object* v_res_3484_;
v_res_3484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(lean_box(0), v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
stack->m_obj
 = v_res_3484_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___boxed(lean_object* v_00_u03b1_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0(v_00_u03b1_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
return v_res_3495_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_elabArg(lean_object* v_stx_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v___x_3523_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_3524_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
lean_inc(v_stx_3513_);
v___x_3525_ = l_Lean_Syntax_isOfKind(v_stx_3513_, v___x_3524_);
if (v___x_3525_ == 0)
{
lean_object* v___x_3526_; 
lean_dec(v_stx_3513_);
v___x_3526_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3526_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3553_; lean_object* v_neg_x3f_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; 
v___x_3527_ = lean_unsigned_to_nat(1u);
v___x_3528_ = l_Lean_Syntax_getArg(v_stx_3513_, v___x_3527_);
lean_dec(v_stx_3513_);
v___x_3529_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__3));
lean_inc(v___x_3528_);
v___x_3530_ = l_Lean_Syntax_isOfKind(v___x_3528_, v___x_3529_);
if (v___x_3530_ == 0)
{
lean_object* v___x_3571_; 
lean_dec(v___x_3528_);
v___x_3571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3571_;
}
else
{
lean_object* v___x_3572_; lean_object* v_tk_x3f_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3572_ = lean_unsigned_to_nat(0u);
v___x_3590_ = l_Lean_Syntax_getArg(v___x_3528_, v___x_3572_);
v___x_3591_ = l_Lean_Syntax_isNone(v___x_3590_);
if (v___x_3591_ == 0)
{
uint8_t v___x_3592_; 
lean_inc(v___x_3590_);
v___x_3592_ = l_Lean_Syntax_matchesNull(v___x_3590_, v___x_3527_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; 
lean_dec(v___x_3590_);
lean_dec(v___x_3528_);
v___x_3593_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3593_;
}
else
{
lean_object* v_tk_x3f_3594_; lean_object* v___x_3595_; 
v_tk_x3f_3594_ = l_Lean_Syntax_getArg(v___x_3590_, v___x_3572_);
lean_dec(v___x_3590_);
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_tk_x3f_3594_);
v_tk_x3f_3574_ = v___x_3595_;
v___y_3575_ = v_a_3514_;
v___y_3576_ = v_a_3515_;
v___y_3577_ = v_a_3516_;
v___y_3578_ = v_a_3517_;
v___y_3579_ = v_a_3518_;
v___y_3580_ = v_a_3519_;
v___y_3581_ = v_a_3520_;
v___y_3582_ = v_a_3521_;
goto v___jp_3573_;
}
}
else
{
lean_object* v___x_3596_; 
lean_dec(v___x_3590_);
v___x_3596_ = lean_box(0);
v_tk_x3f_3574_ = v___x_3596_;
v___y_3575_ = v_a_3514_;
v___y_3576_ = v_a_3515_;
v___y_3577_ = v_a_3516_;
v___y_3578_ = v_a_3517_;
v___y_3579_ = v_a_3518_;
v___y_3580_ = v_a_3519_;
v___y_3581_ = v_a_3520_;
v___y_3582_ = v_a_3521_;
goto v___jp_3573_;
}
v___jp_3573_:
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = l_Lean_Syntax_getArg(v___x_3528_, v___x_3527_);
v___x_3584_ = l_Lean_Syntax_isNone(v___x_3583_);
if (v___x_3584_ == 0)
{
uint8_t v___x_3585_; 
lean_inc(v___x_3583_);
v___x_3585_ = l_Lean_Syntax_matchesNull(v___x_3583_, v___x_3527_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; 
lean_dec(v___x_3583_);
lean_dec(v_tk_x3f_3574_);
lean_dec(v___x_3528_);
v___x_3586_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3586_;
}
else
{
lean_object* v_neg_x3f_3587_; lean_object* v___x_3588_; 
v_neg_x3f_3587_ = l_Lean_Syntax_getArg(v___x_3583_, v___x_3572_);
lean_dec(v___x_3583_);
v___x_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3588_, 0, v_neg_x3f_3587_);
v___y_3553_ = v_tk_x3f_3574_;
v_neg_x3f_3554_ = v___x_3588_;
v___y_3555_ = v___y_3575_;
v___y_3556_ = v___y_3576_;
v___y_3557_ = v___y_3577_;
v___y_3558_ = v___y_3578_;
v___y_3559_ = v___y_3579_;
v___y_3560_ = v___y_3580_;
v___y_3561_ = v___y_3581_;
v___y_3562_ = v___y_3582_;
goto v___jp_3552_;
}
}
else
{
lean_object* v___x_3589_; 
lean_dec(v___x_3583_);
v___x_3589_ = lean_box(0);
v___y_3553_ = v_tk_x3f_3574_;
v_neg_x3f_3554_ = v___x_3589_;
v___y_3555_ = v___y_3575_;
v___y_3556_ = v___y_3576_;
v___y_3557_ = v___y_3577_;
v___y_3558_ = v___y_3578_;
v___y_3559_ = v___y_3579_;
v___y_3560_ = v___y_3580_;
v___y_3561_ = v___y_3581_;
v___y_3562_ = v___y_3582_;
goto v___jp_3552_;
}
}
}
v___jp_3531_:
{
if (lean_obj_tag(v___y_3534_) == 0)
{
uint8_t v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = 0;
v___x_3540_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3523_, v___y_3538_, v___x_3539_, v___y_3535_, v___y_3537_, v___y_3532_, v___y_3536_, v___y_3533_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; 
lean_dec_ref_known(v___y_3534_, 1);
v___x_3541_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3523_, v___y_3538_, v___x_3530_, v___y_3535_, v___y_3537_, v___y_3532_, v___y_3536_, v___y_3533_);
return v___x_3541_;
}
}
v___jp_3542_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = l_Lean_TSyntax_getNat(v___y_3544_);
lean_dec(v___y_3544_);
v___x_3551_ = lean_nat_to_int(v___x_3550_);
v___y_3532_ = v___y_3543_;
v___y_3533_ = v___y_3545_;
v___y_3534_ = v___y_3546_;
v___y_3535_ = v___y_3547_;
v___y_3536_ = v___y_3548_;
v___y_3537_ = v___y_3549_;
v___y_3538_ = v___x_3551_;
goto v___jp_3531_;
}
v___jp_3552_:
{
lean_object* v___x_3563_; lean_object* v_i_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3563_ = lean_unsigned_to_nat(2u);
v_i_3564_ = l_Lean_Syntax_getArg(v___x_3528_, v___x_3563_);
lean_dec(v___x_3528_);
v___x_3565_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__5));
lean_inc(v_i_3564_);
v___x_3566_ = l_Lean_Syntax_isOfKind(v_i_3564_, v___x_3565_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; 
lean_dec(v_i_3564_);
lean_dec(v_neg_x3f_3554_);
lean_dec(v___y_3553_);
v___x_3567_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_elabArg_spec__0___redArg();
return v___x_3567_;
}
else
{
if (lean_obj_tag(v_neg_x3f_3554_) == 0)
{
v___y_3543_ = v___y_3560_;
v___y_3544_ = v_i_3564_;
v___y_3545_ = v___y_3562_;
v___y_3546_ = v___y_3553_;
v___y_3547_ = v___y_3556_;
v___y_3548_ = v___y_3561_;
v___y_3549_ = v___y_3559_;
goto v___jp_3542_;
}
else
{
lean_dec_ref_known(v_neg_x3f_3554_, 1);
if (v___x_3530_ == 0)
{
v___y_3543_ = v___y_3560_;
v___y_3544_ = v_i_3564_;
v___y_3545_ = v___y_3562_;
v___y_3546_ = v___y_3553_;
v___y_3547_ = v___y_3556_;
v___y_3548_ = v___y_3561_;
v___y_3549_ = v___y_3559_;
goto v___jp_3542_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = l_Lean_TSyntax_getNat(v_i_3564_);
lean_dec(v_i_3564_);
v___x_3569_ = lean_nat_to_int(v___x_3568_);
v___x_3570_ = lean_int_neg(v___x_3569_);
lean_dec(v___x_3569_);
v___y_3532_ = v___y_3560_;
v___y_3533_ = v___y_3562_;
v___y_3534_ = v___y_3553_;
v___y_3535_ = v___y_3556_;
v___y_3536_ = v___y_3561_;
v___y_3537_ = v___y_3559_;
v___y_3538_ = v___x_3570_;
goto v___jp_3531_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_elabArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_3513_ = stack[0].m_obj;
lean_object* v_a_3514_ = stack[1].m_obj;
lean_object* v_a_3515_ = stack[2].m_obj;
lean_object* v_a_3516_ = stack[3].m_obj;
lean_object* v_a_3517_ = stack[4].m_obj;
lean_object* v_a_3518_ = stack[5].m_obj;
lean_object* v_a_3519_ = stack[6].m_obj;
lean_object* v_a_3520_ = stack[7].m_obj;
lean_object* v_a_3521_ = stack[8].m_obj;
lean_object* v_res_3597_;
v_res_3597_ = l_Lean_Elab_Tactic_Conv_elabArg(v_stx_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
stack->m_obj
 = v_res_3597_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_elabArg___boxed(lean_object* v_stx_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Lean_Elab_Tactic_Conv_elabArg(v_stx_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3608_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1(){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3617_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3618_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__1));
v___x_3619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___closed__1));
v___x_3620_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_elabArg___boxed), 10, 0);
v___x_3621_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3617_, v___x_3618_, v___x_3619_, v___x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3622_;
v_res_3622_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
stack->m_obj
 = v_res_3622_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1___boxed(lean_object* v_a_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_elabArg___regBuiltin_Lean_Elab_Tactic_Conv_elabArg__1();
return v_res_3624_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg(lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; lean_object* v___x_3635_; 
v___x_3632_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalLhs___redArg___closed__0));
v___x_3633_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_congrArgN___lam__0___closed__1);
v___x_3634_ = 0;
v___x_3635_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3632_, v___x_3633_, v___x_3634_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
return v___x_3635_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalLhs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3626_ = stack[0].m_obj;
lean_object* v_a_3627_ = stack[1].m_obj;
lean_object* v_a_3628_ = stack[2].m_obj;
lean_object* v_a_3629_ = stack[3].m_obj;
lean_object* v_a_3630_ = stack[4].m_obj;
lean_object* v_res_3636_;
v_res_3636_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
stack->m_obj
 = v_res_3636_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___redArg___boxed(lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
lean_dec(v_a_3637_);
return v_res_3643_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalLhs(lean_object* v_x_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_Elab_Tactic_Conv_evalLhs___redArg(v_a_3646_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
return v___x_3654_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalLhs_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3644_ = stack[0].m_obj;
lean_object* v_a_3645_ = stack[1].m_obj;
lean_object* v_a_3646_ = stack[2].m_obj;
lean_object* v_a_3647_ = stack[3].m_obj;
lean_object* v_a_3648_ = stack[4].m_obj;
lean_object* v_a_3649_ = stack[5].m_obj;
lean_object* v_a_3650_ = stack[6].m_obj;
lean_object* v_a_3651_ = stack[7].m_obj;
lean_object* v_a_3652_ = stack[8].m_obj;
lean_object* v_res_3655_;
v_res_3655_ = l_Lean_Elab_Tactic_Conv_evalLhs(v_x_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
stack->m_obj
 = v_res_3655_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalLhs___boxed(lean_object* v_x_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_Elab_Tactic_Conv_evalLhs(v_x_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_);
lean_dec(v_a_3664_);
lean_dec_ref(v_a_3663_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_x_3656_);
return v_res_3666_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1(){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3681_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__0));
v___x_3683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3684_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalLhs___boxed), 10, 0);
v___x_3685_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3681_, v___x_3682_, v___x_3683_, v___x_3684_);
return v___x_3685_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3686_;
v_res_3686_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
stack->m_obj
 = v_res_3686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___boxed(lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1();
return v_res_3688_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3(){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs__1___closed__2));
v___x_3716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___closed__6));
v___x_3717_ = l_Lean_addBuiltinDeclarationRanges(v___x_3715_, v___x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3718_;
v_res_3718_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
stack->m_obj
 = v_res_3718_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3___boxed(lean_object* v_a_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalLhs___regBuiltin_Lean_Elab_Tactic_Conv_evalLhs_declRange__3();
return v_res_3720_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrArgN_applyArgs___closed__7);
v___x_3723_ = lean_int_neg(v___x_3722_);
return v___x_3723_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg(lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; 
v___x_3730_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__0));
v___x_3731_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1, &l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_evalRhs___redArg___closed__1);
v___x_3732_ = 0;
v___x_3733_ = l_Lean_Elab_Tactic_Conv_evalArg___redArg(v___x_3730_, v___x_3731_, v___x_3732_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
return v___x_3733_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalRhs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3724_ = stack[0].m_obj;
lean_object* v_a_3725_ = stack[1].m_obj;
lean_object* v_a_3726_ = stack[2].m_obj;
lean_object* v_a_3727_ = stack[3].m_obj;
lean_object* v_a_3728_ = stack[4].m_obj;
lean_object* v_res_3734_;
v_res_3734_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_);
stack->m_obj
 = v_res_3734_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___redArg___boxed(lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
return v_res_3741_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalRhs(lean_object* v_x_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Lean_Elab_Tactic_Conv_evalRhs___redArg(v_a_3744_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
return v___x_3752_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalRhs_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3742_ = stack[0].m_obj;
lean_object* v_a_3743_ = stack[1].m_obj;
lean_object* v_a_3744_ = stack[2].m_obj;
lean_object* v_a_3745_ = stack[3].m_obj;
lean_object* v_a_3746_ = stack[4].m_obj;
lean_object* v_a_3747_ = stack[5].m_obj;
lean_object* v_a_3748_ = stack[6].m_obj;
lean_object* v_a_3749_ = stack[7].m_obj;
lean_object* v_a_3750_ = stack[8].m_obj;
lean_object* v_res_3753_;
v_res_3753_ = l_Lean_Elab_Tactic_Conv_evalRhs(v_x_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
stack->m_obj
 = v_res_3753_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalRhs___boxed(lean_object* v_x_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Elab_Tactic_Conv_evalRhs(v_x_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
lean_dec(v_x_3754_);
return v_res_3764_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1(){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3779_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3780_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__0));
v___x_3781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3782_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalRhs___boxed), 10, 0);
v___x_3783_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3779_, v___x_3780_, v___x_3781_, v___x_3782_);
return v___x_3783_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3784_;
v_res_3784_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
stack->m_obj
 = v_res_3784_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___boxed(lean_object* v_a_3785_){
_start:
{
lean_object* v_res_3786_; 
v_res_3786_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1();
return v_res_3786_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3(){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs__1___closed__2));
v___x_3814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___closed__6));
v___x_3815_ = l_Lean_addBuiltinDeclarationRanges(v___x_3813_, v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3816_;
v_res_3816_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
stack->m_obj
 = v_res_3816_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3___boxed(lean_object* v_a_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalRhs___regBuiltin_Lean_Elab_Tactic_Conv_evalRhs_declRange__3();
return v_res_3818_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(lean_object* v_e_3819_, lean_object* v___y_3820_){
_start:
{
uint8_t v___x_3822_; 
v___x_3822_ = l_Lean_Expr_hasMVar(v_e_3819_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; 
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v_e_3819_);
return v___x_3823_;
}
else
{
lean_object* v___x_3824_; lean_object* v_mctx_3825_; lean_object* v___x_3826_; lean_object* v_fst_3827_; lean_object* v_snd_3828_; lean_object* v___x_3829_; lean_object* v_cache_3830_; lean_object* v_zetaDeltaFVarIds_3831_; lean_object* v_postponed_3832_; lean_object* v_diag_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3842_; 
v___x_3824_ = lean_st_ref_get(v___y_3820_);
v_mctx_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc_ref(v_mctx_3825_);
lean_dec(v___x_3824_);
v___x_3826_ = l_Lean_instantiateMVarsCore(v_mctx_3825_, v_e_3819_);
v_fst_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_fst_3827_);
v_snd_3828_ = lean_ctor_get(v___x_3826_, 1);
lean_inc(v_snd_3828_);
lean_dec_ref(v___x_3826_);
v___x_3829_ = lean_st_ref_take(v___y_3820_);
v_cache_3830_ = lean_ctor_get(v___x_3829_, 1);
v_zetaDeltaFVarIds_3831_ = lean_ctor_get(v___x_3829_, 2);
v_postponed_3832_ = lean_ctor_get(v___x_3829_, 3);
v_diag_3833_ = lean_ctor_get(v___x_3829_, 4);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3842_ == 0)
{
lean_object* v_unused_3843_; 
v_unused_3843_ = lean_ctor_get(v___x_3829_, 0);
lean_dec(v_unused_3843_);
v___x_3835_ = v___x_3829_;
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_diag_3833_);
lean_inc(v_postponed_3832_);
lean_inc(v_zetaDeltaFVarIds_3831_);
lean_inc(v_cache_3830_);
lean_dec(v___x_3829_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3842_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v_snd_3828_);
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_snd_3828_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_cache_3830_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v_zetaDeltaFVarIds_3831_);
lean_ctor_set(v_reuseFailAlloc_3841_, 3, v_postponed_3832_);
lean_ctor_set(v_reuseFailAlloc_3841_, 4, v_diag_3833_);
v___x_3838_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3839_ = lean_st_ref_put(v___y_3820_, v___x_3838_);
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v_fst_3827_);
return v___x_3840_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3819_ = stack[0].m_obj;
lean_object* v___y_3820_ = stack[1].m_obj;
lean_object* v_res_3844_;
v_res_3844_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3819_, v___y_3820_);
stack->m_obj
 = v_res_3844_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg___boxed(lean_object* v_e_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3845_, v___y_3846_);
lean_dec(v___y_3846_);
return v_res_3848_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(lean_object* v_e_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_e_3849_, v___y_3855_);
return v___x_3859_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3849_ = stack[0].m_obj;
lean_object* v___y_3850_ = stack[1].m_obj;
lean_object* v___y_3851_ = stack[2].m_obj;
lean_object* v___y_3852_ = stack[3].m_obj;
lean_object* v___y_3853_ = stack[4].m_obj;
lean_object* v___y_3854_ = stack[5].m_obj;
lean_object* v___y_3855_ = stack[6].m_obj;
lean_object* v___y_3856_ = stack[7].m_obj;
lean_object* v___y_3857_ = stack[8].m_obj;
lean_object* v_res_3860_;
v_res_3860_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(v_e_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
stack->m_obj
 = v_res_3860_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___boxed(lean_object* v_e_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0(v_e_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
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
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(lean_object* v_x_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
lean_inc(v___y_3876_);
lean_inc_ref(v___y_3875_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3873_);
v___x_3882_ = lean_apply_9(v_x_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, lean_box(0));
return v___x_3882_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3872_ = stack[0].m_obj;
lean_object* v___y_3873_ = stack[1].m_obj;
lean_object* v___y_3874_ = stack[2].m_obj;
lean_object* v___y_3875_ = stack[3].m_obj;
lean_object* v___y_3876_ = stack[4].m_obj;
lean_object* v___y_3877_ = stack[5].m_obj;
lean_object* v___y_3878_ = stack[6].m_obj;
lean_object* v___y_3879_ = stack[7].m_obj;
lean_object* v___y_3880_ = stack[8].m_obj;
lean_object* v_res_3883_;
v_res_3883_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(v_x_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
stack->m_obj
 = v_res_3883_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed(lean_object* v_x_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0(v_x_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3894_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(lean_object* v_mvarId_3895_, lean_object* v_x_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___f_3906_; lean_object* v___x_3907_; 
lean_inc(v___y_3900_);
lean_inc_ref(v___y_3899_);
lean_inc(v___y_3898_);
lean_inc_ref(v___y_3897_);
v___f_3906_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3906_, 0, v_x_3896_);
lean_closure_set(v___f_3906_, 1, v___y_3897_);
lean_closure_set(v___f_3906_, 2, v___y_3898_);
lean_closure_set(v___f_3906_, 3, v___y_3899_);
lean_closure_set(v___f_3906_, 4, v___y_3900_);
v___x_3907_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3895_, v___f_3906_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
if (lean_obj_tag(v___x_3907_) == 0)
{
return v___x_3907_;
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3895_ = stack[0].m_obj;
lean_object* v_x_3896_ = stack[1].m_obj;
lean_object* v___y_3897_ = stack[2].m_obj;
lean_object* v___y_3898_ = stack[3].m_obj;
lean_object* v___y_3899_ = stack[4].m_obj;
lean_object* v___y_3900_ = stack[5].m_obj;
lean_object* v___y_3901_ = stack[6].m_obj;
lean_object* v___y_3902_ = stack[7].m_obj;
lean_object* v___y_3903_ = stack[8].m_obj;
lean_object* v___y_3904_ = stack[9].m_obj;
lean_object* v_res_3916_;
v_res_3916_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3895_, v_x_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
stack->m_obj
 = v_res_3916_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg___boxed(lean_object* v_mvarId_3917_, lean_object* v_x_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3917_, v_x_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
return v_res_3928_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_object* v_00_u03b1_3929_, lean_object* v_mvarId_3930_, lean_object* v_x_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_mvarId_3930_, v_x_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3941_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3930_ = stack[1].m_obj;
lean_object* v_x_3931_ = stack[2].m_obj;
lean_object* v___y_3932_ = stack[3].m_obj;
lean_object* v___y_3933_ = stack[4].m_obj;
lean_object* v___y_3934_ = stack[5].m_obj;
lean_object* v___y_3935_ = stack[6].m_obj;
lean_object* v___y_3936_ = stack[7].m_obj;
lean_object* v___y_3937_ = stack[8].m_obj;
lean_object* v___y_3938_ = stack[9].m_obj;
lean_object* v___y_3939_ = stack[10].m_obj;
lean_object* v_res_3942_;
v_res_3942_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(lean_box(0), v_mvarId_3930_, v_x_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
stack->m_obj
 = v_res_3942_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___boxed(lean_object* v_00_u03b1_3943_, lean_object* v_mvarId_3944_, lean_object* v_x_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3(v_00_u03b1_3943_, v_mvarId_3944_, v_x_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3955_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(lean_object* v_msg_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_ref_3962_; lean_object* v___x_3963_; lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3972_; 
v_ref_3962_ = lean_ctor_get(v___y_3959_, 2);
v___x_3963_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0_spec__0(v_msg_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3972_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3972_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3970_; 
lean_inc(v_ref_3962_);
v___x_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3968_, 0, v_ref_3962_);
lean_ctor_set(v___x_3968_, 1, v_a_3964_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set_tag(v___x_3966_, 1);
lean_ctor_set(v___x_3966_, 0, v___x_3968_);
v___x_3970_ = v___x_3966_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3968_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3956_ = stack[0].m_obj;
lean_object* v___y_3957_ = stack[1].m_obj;
lean_object* v___y_3958_ = stack[2].m_obj;
lean_object* v___y_3959_ = stack[3].m_obj;
lean_object* v___y_3960_ = stack[4].m_obj;
lean_object* v_res_3973_;
v_res_3973_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
stack->m_obj
 = v_res_3973_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg___boxed(lean_object* v_msg_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
return v_res_3980_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(lean_object* v_mvarId_3981_, lean_object* v_val_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v_mctx_3986_; lean_object* v_cache_3987_; lean_object* v_zetaDeltaFVarIds_3988_; lean_object* v_postponed_3989_; lean_object* v_diag_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4020_; 
v___x_3985_ = lean_st_ref_take(v___y_3983_);
v_mctx_3986_ = lean_ctor_get(v___x_3985_, 0);
v_cache_3987_ = lean_ctor_get(v___x_3985_, 1);
v_zetaDeltaFVarIds_3988_ = lean_ctor_get(v___x_3985_, 2);
v_postponed_3989_ = lean_ctor_get(v___x_3985_, 3);
v_diag_3990_ = lean_ctor_get(v___x_3985_, 4);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_3992_ = v___x_3985_;
v_isShared_3993_ = v_isSharedCheck_4020_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_diag_3990_);
lean_inc(v_postponed_3989_);
lean_inc(v_zetaDeltaFVarIds_3988_);
lean_inc(v_cache_3987_);
lean_inc(v_mctx_3986_);
lean_dec(v___x_3985_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4020_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v_depth_3994_; lean_object* v_levelAssignDepth_3995_; lean_object* v_lmvarCounter_3996_; lean_object* v_mvarCounter_3997_; lean_object* v_lDecls_3998_; lean_object* v_decls_3999_; lean_object* v_userNames_4000_; lean_object* v_lAssignment_4001_; lean_object* v_eAssignment_4002_; lean_object* v_dAssignment_4003_; lean_object* v_instanceTypedMVars_4004_; lean_object* v_synthNormMemo_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4019_; 
v_depth_3994_ = lean_ctor_get(v_mctx_3986_, 0);
v_levelAssignDepth_3995_ = lean_ctor_get(v_mctx_3986_, 1);
v_lmvarCounter_3996_ = lean_ctor_get(v_mctx_3986_, 2);
v_mvarCounter_3997_ = lean_ctor_get(v_mctx_3986_, 3);
v_lDecls_3998_ = lean_ctor_get(v_mctx_3986_, 4);
v_decls_3999_ = lean_ctor_get(v_mctx_3986_, 5);
v_userNames_4000_ = lean_ctor_get(v_mctx_3986_, 6);
v_lAssignment_4001_ = lean_ctor_get(v_mctx_3986_, 7);
v_eAssignment_4002_ = lean_ctor_get(v_mctx_3986_, 8);
v_dAssignment_4003_ = lean_ctor_get(v_mctx_3986_, 9);
v_instanceTypedMVars_4004_ = lean_ctor_get(v_mctx_3986_, 10);
v_synthNormMemo_4005_ = lean_ctor_get(v_mctx_3986_, 11);
v_isSharedCheck_4019_ = !lean_is_exclusive(v_mctx_3986_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4007_ = v_mctx_3986_;
v_isShared_4008_ = v_isSharedCheck_4019_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_synthNormMemo_4005_);
lean_inc(v_instanceTypedMVars_4004_);
lean_inc(v_dAssignment_4003_);
lean_inc(v_eAssignment_4002_);
lean_inc(v_lAssignment_4001_);
lean_inc(v_userNames_4000_);
lean_inc(v_decls_3999_);
lean_inc(v_lDecls_3998_);
lean_inc(v_mvarCounter_3997_);
lean_inc(v_lmvarCounter_3996_);
lean_inc(v_levelAssignDepth_3995_);
lean_inc(v_depth_3994_);
lean_dec(v_mctx_3986_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4019_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4009_ = lean_box(0);
v___x_4010_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1_spec__1___redArg(v_eAssignment_4002_, v_mvarId_3981_, v_val_3982_);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 8, v___x_4010_);
v___x_4012_ = v___x_4007_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_depth_3994_);
lean_ctor_set(v_reuseFailAlloc_4018_, 1, v_levelAssignDepth_3995_);
lean_ctor_set(v_reuseFailAlloc_4018_, 2, v_lmvarCounter_3996_);
lean_ctor_set(v_reuseFailAlloc_4018_, 3, v_mvarCounter_3997_);
lean_ctor_set(v_reuseFailAlloc_4018_, 4, v_lDecls_3998_);
lean_ctor_set(v_reuseFailAlloc_4018_, 5, v_decls_3999_);
lean_ctor_set(v_reuseFailAlloc_4018_, 6, v_userNames_4000_);
lean_ctor_set(v_reuseFailAlloc_4018_, 7, v_lAssignment_4001_);
lean_ctor_set(v_reuseFailAlloc_4018_, 8, v___x_4010_);
lean_ctor_set(v_reuseFailAlloc_4018_, 9, v_dAssignment_4003_);
lean_ctor_set(v_reuseFailAlloc_4018_, 10, v_instanceTypedMVars_4004_);
lean_ctor_set(v_reuseFailAlloc_4018_, 11, v_synthNormMemo_4005_);
v___x_4012_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4014_; 
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4012_);
v___x_4014_ = v___x_3992_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_cache_3987_);
lean_ctor_set(v_reuseFailAlloc_4017_, 2, v_zetaDeltaFVarIds_3988_);
lean_ctor_set(v_reuseFailAlloc_4017_, 3, v_postponed_3989_);
lean_ctor_set(v_reuseFailAlloc_4017_, 4, v_diag_3990_);
v___x_4014_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4015_ = lean_st_ref_put(v___y_3983_, v___x_4014_);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4009_);
return v___x_4016_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3981_ = stack[0].m_obj;
lean_object* v_val_3982_ = stack[1].m_obj;
lean_object* v___y_3983_ = stack[2].m_obj;
lean_object* v_res_4021_;
v_res_4021_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_3981_, v_val_3982_, v___y_3983_);
stack->m_obj
 = v_res_4021_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg___boxed(lean_object* v_mvarId_4022_, lean_object* v_val_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_4022_, v_val_4023_, v___y_4024_);
lean_dec(v___y_4024_);
return v_res_4026_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__1));
v___x_4030_ = l_Lean_stringToMessageData(v___x_4029_);
return v___x_4030_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(lean_object* v_a_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
lean_inc(v_a_4031_);
v___x_4041_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_a_4031_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v_fst_4043_; lean_object* v_snd_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4096_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v___x_4041_, 1);
v_fst_4043_ = lean_ctor_get(v_a_4042_, 0);
v_snd_4044_ = lean_ctor_get(v_a_4042_, 1);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_a_4042_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4046_ = v_a_4042_;
v_isShared_4047_ = v_isSharedCheck_4096_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_snd_4044_);
lean_inc(v_fst_4043_);
lean_dec(v_a_4042_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4096_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4048_; lean_object* v_a_4049_; lean_object* v___x_4050_; 
v___x_4048_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_evalFun_spec__0___redArg(v_fst_4043_, v___y_4037_);
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref(v___x_4048_);
v___x_4050_ = l_Lean_Expr_cleanupAnnotations(v_a_4049_);
if (lean_obj_tag(v___x_4050_) == 5)
{
lean_object* v_fn_4051_; lean_object* v_arg_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
lean_del_object(v___x_4046_);
v_fn_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc_ref(v_fn_4051_);
v_arg_4052_ = lean_ctor_get(v___x_4050_, 1);
lean_inc_ref(v_arg_4052_);
lean_dec_ref_known(v___x_4050_, 2);
v___x_4053_ = lean_box(0);
v___x_4054_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v_fn_4051_, v___x_4053_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v_fst_4056_; lean_object* v_snd_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4081_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4055_);
lean_dec_ref_known(v___x_4054_, 1);
v_fst_4056_ = lean_ctor_get(v_a_4055_, 0);
v_snd_4057_ = lean_ctor_get(v_a_4055_, 1);
v_isSharedCheck_4081_ = !lean_is_exclusive(v_a_4055_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4059_ = v_a_4055_;
v_isShared_4060_ = v_isSharedCheck_4081_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_snd_4057_);
lean_inc(v_fst_4056_);
lean_dec(v_a_4055_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4081_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; 
lean_inc_ref(v_arg_4052_);
lean_inc(v_snd_4057_);
v___x_4061_ = l_Lean_Meta_mkCongrFun(v_snd_4057_, v_arg_4052_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v___x_4063_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_a_4031_, v_a_4062_, v___y_4037_);
lean_dec_ref(v___x_4063_);
v___x_4064_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__0));
v___x_4065_ = l_Lean_Expr_app___override(v_fst_4056_, v_arg_4052_);
v___x_4066_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_4064_, v_snd_4044_, v___x_4065_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_dec_ref_known(v___x_4066_, 1);
v___x_4067_ = l_Lean_Expr_mvarId_x21(v_snd_4057_);
lean_dec(v_snd_4057_);
v___x_4068_ = lean_box(0);
if (v_isShared_4060_ == 0)
{
lean_ctor_set_tag(v___x_4059_, 1);
lean_ctor_set(v___x_4059_, 1, v___x_4068_);
lean_ctor_set(v___x_4059_, 0, v___x_4067_);
v___x_4070_ = v___x_4059_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_4070_, v___y_4033_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
return v___x_4071_;
}
}
else
{
lean_del_object(v___x_4059_);
lean_dec(v_snd_4057_);
return v___x_4066_;
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_del_object(v___x_4059_);
lean_dec(v_snd_4057_);
lean_dec(v_fst_4056_);
lean_dec_ref(v_arg_4052_);
lean_dec(v_snd_4044_);
lean_dec(v_a_4031_);
v_a_4073_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4061_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4061_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec_ref(v_arg_4052_);
lean_dec(v_snd_4044_);
lean_dec(v_a_4031_);
v_a_4082_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4054_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4054_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
else
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4093_; 
lean_dec(v_snd_4044_);
lean_dec(v_a_4031_);
v___x_4090_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2, &l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___closed__2);
v___x_4091_ = l_Lean_indentExpr(v___x_4050_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set_tag(v___x_4046_, 7);
lean_ctor_set(v___x_4046_, 1, v___x_4091_);
lean_ctor_set(v___x_4046_, 0, v___x_4090_);
v___x_4093_ = v___x_4046_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
lean_object* v___x_4094_; 
v___x_4094_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v___x_4093_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
return v___x_4094_;
}
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_a_4031_);
v_a_4097_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4041_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4041_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4031_ = stack[0].m_obj;
lean_object* v___y_4032_ = stack[1].m_obj;
lean_object* v___y_4033_ = stack[2].m_obj;
lean_object* v___y_4034_ = stack[3].m_obj;
lean_object* v___y_4035_ = stack[4].m_obj;
lean_object* v___y_4036_ = stack[5].m_obj;
lean_object* v___y_4037_ = stack[6].m_obj;
lean_object* v___y_4038_ = stack[7].m_obj;
lean_object* v___y_4039_ = stack[8].m_obj;
lean_object* v_res_4105_;
v_res_4105_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(v_a_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
stack->m_obj
 = v_res_4105_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed(lean_object* v_a_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0(v_a_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4116_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg(lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_4118_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___f_4128_; lean_object* v___x_4129_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc_n(v_a_4127_, 2);
lean_dec_ref_known(v___x_4126_, 1);
v___f_4128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4128_, 0, v_a_4127_);
v___x_4129_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalFun_spec__3___redArg(v_a_4127_, v___f_4128_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
return v___x_4129_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
v_a_4130_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4126_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4126_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalFun___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4117_ = stack[0].m_obj;
lean_object* v_a_4118_ = stack[1].m_obj;
lean_object* v_a_4119_ = stack[2].m_obj;
lean_object* v_a_4120_ = stack[3].m_obj;
lean_object* v_a_4121_ = stack[4].m_obj;
lean_object* v_a_4122_ = stack[5].m_obj;
lean_object* v_a_4123_ = stack[6].m_obj;
lean_object* v_a_4124_ = stack[7].m_obj;
lean_object* v_res_4138_;
v_res_4138_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
stack->m_obj
 = v_res_4138_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___redArg___boxed(lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
return v_res_4148_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalFun(lean_object* v_x_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Lean_Elab_Tactic_Conv_evalFun___redArg(v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
return v___x_4159_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalFun_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4149_ = stack[0].m_obj;
lean_object* v_a_4150_ = stack[1].m_obj;
lean_object* v_a_4151_ = stack[2].m_obj;
lean_object* v_a_4152_ = stack[3].m_obj;
lean_object* v_a_4153_ = stack[4].m_obj;
lean_object* v_a_4154_ = stack[5].m_obj;
lean_object* v_a_4155_ = stack[6].m_obj;
lean_object* v_a_4156_ = stack[7].m_obj;
lean_object* v_a_4157_ = stack[8].m_obj;
lean_object* v_res_4160_;
v_res_4160_ = l_Lean_Elab_Tactic_Conv_evalFun(v_x_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
stack->m_obj
 = v_res_4160_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalFun___boxed(lean_object* v_x_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Elab_Tactic_Conv_evalFun(v_x_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
lean_dec_ref(v_a_4162_);
lean_dec(v_x_4161_);
return v_res_4171_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(lean_object* v_mvarId_4172_, lean_object* v_val_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___redArg(v_mvarId_4172_, v_val_4173_, v___y_4179_);
return v___x_4183_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4172_ = stack[0].m_obj;
lean_object* v_val_4173_ = stack[1].m_obj;
lean_object* v___y_4174_ = stack[2].m_obj;
lean_object* v___y_4175_ = stack[3].m_obj;
lean_object* v___y_4176_ = stack[4].m_obj;
lean_object* v___y_4177_ = stack[5].m_obj;
lean_object* v___y_4178_ = stack[6].m_obj;
lean_object* v___y_4179_ = stack[7].m_obj;
lean_object* v___y_4180_ = stack[8].m_obj;
lean_object* v___y_4181_ = stack[9].m_obj;
lean_object* v_res_4184_;
v_res_4184_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(v_mvarId_4172_, v_val_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
stack->m_obj
 = v_res_4184_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1___boxed(lean_object* v_mvarId_4185_, lean_object* v_val_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalFun_spec__1(v_mvarId_4185_, v_val_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
return v_res_4196_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_object* v_00_u03b1_4197_, lean_object* v_msg_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___redArg(v_msg_4198_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
return v___x_4208_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4198_ = stack[1].m_obj;
lean_object* v___y_4199_ = stack[2].m_obj;
lean_object* v___y_4200_ = stack[3].m_obj;
lean_object* v___y_4201_ = stack[4].m_obj;
lean_object* v___y_4202_ = stack[5].m_obj;
lean_object* v___y_4203_ = stack[6].m_obj;
lean_object* v___y_4204_ = stack[7].m_obj;
lean_object* v___y_4205_ = stack[8].m_obj;
lean_object* v___y_4206_ = stack[9].m_obj;
lean_object* v_res_4209_;
v_res_4209_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(lean_box(0), v_msg_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
stack->m_obj
 = v_res_4209_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2___boxed(lean_object* v_00_u03b1_4210_, lean_object* v_msg_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalFun_spec__2(v_00_u03b1_4210_, v_msg_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
return v_res_4221_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1(){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4236_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_4237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__0));
v___x_4238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4239_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalFun___boxed), 10, 0);
v___x_4240_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4236_, v___x_4237_, v___x_4238_, v___x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4241_;
v_res_4241_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
stack->m_obj
 = v_res_4241_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___boxed(lean_object* v_a_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1();
return v_res_4243_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3(){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4270_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun__1___closed__2));
v___x_4271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___closed__6));
v___x_4272_ = l_Lean_addBuiltinDeclarationRanges(v___x_4270_, v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4273_;
v_res_4273_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
stack->m_obj
 = v_res_4273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3___boxed(lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalFun___regBuiltin_Lean_Elab_Tactic_Conv_evalFun_declRange__3();
return v_res_4275_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__0));
v___x_4278_ = l_Lean_stringToMessageData(v___x_4277_);
return v___x_4278_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(lean_object* v___x_4279_, lean_object* v_declName_4280_, lean_object* v_type_4281_, lean_object* v_value_4282_, lean_object* v_rhs_4283_, lean_object* v_a_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_inc_ref(v_a_4284_);
v___x_4290_ = l_Lean_Expr_app___override(v___x_4279_, v_a_4284_);
lean_inc(v___y_4288_);
lean_inc_ref(v___y_4287_);
lean_inc(v___y_4286_);
lean_inc_ref(v___y_4285_);
v___x_4291_ = lean_infer_type(v___x_4290_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; uint8_t v___x_4297_; uint8_t v___x_4298_; lean_object* v___x_4299_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc_n(v_a_4292_, 2);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = lean_unsigned_to_nat(1u);
v___x_4294_ = lean_mk_empty_array_with_capacity(v___x_4293_);
v___x_4295_ = lean_array_push(v___x_4294_, v_a_4284_);
v___x_4296_ = 0;
v___x_4297_ = 1;
v___x_4298_ = 1;
v___x_4299_ = l_Lean_Meta_mkLambdaFVars(v___x_4295_, v_a_4292_, v___x_4296_, v___x_4297_, v___x_4296_, v___x_4297_, v___x_4298_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4301_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
lean_inc(v_a_4292_);
v___x_4301_ = l_Lean_Meta_getLevel(v_a_4292_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
v___x_4303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_a_4292_);
v___x_4304_ = 0;
v___x_4305_ = lean_box(0);
v___x_4306_ = l_Lean_Meta_mkFreshExprMVar(v___x_4303_, v___x_4304_, v___x_4305_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4308_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v___x_4308_ = l_Lean_Meta_mkLambdaFVars(v___x_4295_, v_a_4307_, v___x_4296_, v___x_4297_, v___x_4296_, v___x_4297_, v___x_4298_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec_ref(v___x_4295_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4342_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4311_ = v___x_4308_;
v_isShared_4312_ = v_isSharedCheck_4342_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4342_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4319_ = l_Lean_Expr_bindingBody_x21(v_a_4309_);
v___x_4320_ = l_Lean_Expr_letE___override(v_declName_4280_, v_type_4281_, v_value_4282_, v___x_4319_, v___x_4296_);
v___x_4321_ = l_Lean_Meta_isExprDefEq(v_rhs_4283_, v___x_4320_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; uint8_t v___x_4323_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
v___x_4323_ = lean_unbox(v_a_4322_);
lean_dec(v_a_4322_);
if (v___x_4323_ == 0)
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_del_object(v___x_4311_);
lean_dec(v_a_4309_);
lean_dec(v_a_4302_);
lean_dec(v_a_4300_);
v___x_4324_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___closed__1);
v___x_4325_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4324_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
v_a_4326_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4325_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4325_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
else
{
goto v___jp_4313_;
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_del_object(v___x_4311_);
lean_dec(v_a_4309_);
lean_dec(v_a_4302_);
lean_dec(v_a_4300_);
v_a_4334_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4321_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4321_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
v___jp_4313_:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4317_; 
v___x_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4314_, 0, v_a_4302_);
lean_ctor_set(v___x_4314_, 1, v_a_4309_);
v___x_4315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4315_, 0, v_a_4300_);
lean_ctor_set(v___x_4315_, 1, v___x_4314_);
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 0, v___x_4315_);
v___x_4317_ = v___x_4311_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v___x_4315_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v_a_4302_);
lean_dec(v_a_4300_);
lean_dec_ref(v_rhs_4283_);
lean_dec_ref(v_value_4282_);
lean_dec_ref(v_type_4281_);
lean_dec(v_declName_4280_);
v_a_4343_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4308_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4308_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v_a_4302_);
lean_dec(v_a_4300_);
lean_dec_ref(v___x_4295_);
lean_dec_ref(v_rhs_4283_);
lean_dec_ref(v_value_4282_);
lean_dec_ref(v_type_4281_);
lean_dec(v_declName_4280_);
v_a_4351_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4306_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4306_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
else
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4366_; 
lean_dec(v_a_4300_);
lean_dec_ref(v___x_4295_);
lean_dec(v_a_4292_);
lean_dec_ref(v_rhs_4283_);
lean_dec_ref(v_value_4282_);
lean_dec_ref(v_type_4281_);
lean_dec(v_declName_4280_);
v_a_4359_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4361_ = v___x_4301_;
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4301_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4366_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___x_4364_; 
if (v_isShared_4362_ == 0)
{
v___x_4364_ = v___x_4361_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v_a_4359_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
}
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
lean_dec_ref(v___x_4295_);
lean_dec(v_a_4292_);
lean_dec_ref(v_rhs_4283_);
lean_dec_ref(v_value_4282_);
lean_dec_ref(v_type_4281_);
lean_dec(v_declName_4280_);
v_a_4367_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4299_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4299_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec_ref(v_a_4284_);
lean_dec_ref(v_rhs_4283_);
lean_dec_ref(v_value_4282_);
lean_dec_ref(v_type_4281_);
lean_dec(v_declName_4280_);
v_a_4375_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4291_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4291_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4279_ = stack[0].m_obj;
lean_object* v_declName_4280_ = stack[1].m_obj;
lean_object* v_type_4281_ = stack[2].m_obj;
lean_object* v_value_4282_ = stack[3].m_obj;
lean_object* v_rhs_4283_ = stack[4].m_obj;
lean_object* v_a_4284_ = stack[5].m_obj;
lean_object* v___y_4285_ = stack[6].m_obj;
lean_object* v___y_4286_ = stack[7].m_obj;
lean_object* v___y_4287_ = stack[8].m_obj;
lean_object* v___y_4288_ = stack[9].m_obj;
lean_object* v_res_4383_;
v_res_4383_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(v___x_4279_, v_declName_4280_, v_type_4281_, v_value_4282_, v_rhs_4283_, v_a_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
stack->m_obj
 = v_res_4383_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed(lean_object* v___x_4384_, lean_object* v_declName_4385_, lean_object* v_type_4386_, lean_object* v_value_4387_, lean_object* v_rhs_4388_, lean_object* v_a_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0(v___x_4384_, v_declName_4385_, v_type_4386_, v_value_4387_, v_rhs_4388_, v_a_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
return v_res_4395_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(lean_object* v___x_4396_, lean_object* v_snd_4397_, lean_object* v_x_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4404_ = lean_unsigned_to_nat(1u);
v___x_4405_ = lean_mk_empty_array_with_capacity(v___x_4404_);
v___x_4406_ = lean_array_push(v___x_4405_, v_x_4398_);
lean_inc_ref_n(v___x_4406_, 2);
v___x_4407_ = l_Lean_Expr_beta(v___x_4396_, v___x_4406_);
v___x_4408_ = l_Lean_Expr_beta(v_snd_4397_, v___x_4406_);
v___x_4409_ = l_Lean_Meta_mkEq(v___x_4407_, v___x_4408_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = lean_box(0);
v___x_4412_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4410_, v___x_4411_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; uint8_t v___x_4414_; uint8_t v___x_4415_; uint8_t v___x_4416_; lean_object* v___x_4417_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc_n(v_a_4413_, 2);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = 0;
v___x_4415_ = 1;
v___x_4416_ = 1;
v___x_4417_ = l_Lean_Meta_mkLambdaFVars(v___x_4406_, v_a_4413_, v___x_4414_, v___x_4415_, v___x_4414_, v___x_4415_, v___x_4416_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec_ref(v___x_4406_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4427_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4420_ = v___x_4417_;
v_isShared_4421_ = v_isSharedCheck_4427_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4417_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4427_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4425_; 
v___x_4422_ = l_Lean_Expr_mvarId_x21(v_a_4413_);
lean_dec(v_a_4413_);
v___x_4423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4423_, 0, v_a_4418_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4423_);
v___x_4425_ = v___x_4420_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4423_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec(v_a_4413_);
v_a_4428_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4417_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4417_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
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
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec_ref(v___x_4406_);
v_a_4436_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4412_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4412_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec_ref(v___x_4406_);
v_a_4444_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4409_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4409_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4396_ = stack[0].m_obj;
lean_object* v_snd_4397_ = stack[1].m_obj;
lean_object* v_x_4398_ = stack[2].m_obj;
lean_object* v___y_4399_ = stack[3].m_obj;
lean_object* v___y_4400_ = stack[4].m_obj;
lean_object* v___y_4401_ = stack[5].m_obj;
lean_object* v___y_4402_ = stack[6].m_obj;
lean_object* v_res_4452_;
v_res_4452_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(v___x_4396_, v_snd_4397_, v_x_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
stack->m_obj
 = v_res_4452_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed(lean_object* v___x_4453_, lean_object* v_snd_4454_, lean_object* v_x_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1(v___x_4453_, v_snd_4454_, v_x_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
return v_res_4461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3(void){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4466_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__2));
v___x_4467_ = l_Lean_stringToMessageData(v___x_4466_);
return v___x_4467_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(lean_object* v_mvarId_4468_, lean_object* v_lhs_4469_, lean_object* v_rhs_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
if (lean_obj_tag(v_lhs_4469_) == 8)
{
lean_object* v_declName_4476_; lean_object* v_type_4477_; lean_object* v_value_4478_; lean_object* v_body_4479_; lean_object* v___x_4480_; 
v_declName_4476_ = lean_ctor_get(v_lhs_4469_, 0);
lean_inc(v_declName_4476_);
v_type_4477_ = lean_ctor_get(v_lhs_4469_, 1);
lean_inc_ref_n(v_type_4477_, 2);
v_value_4478_ = lean_ctor_get(v_lhs_4469_, 2);
lean_inc_ref(v_value_4478_);
v_body_4479_ = lean_ctor_get(v_lhs_4469_, 3);
lean_inc_ref(v_body_4479_);
lean_dec_ref_known(v_lhs_4469_, 4);
v___x_4480_ = l_Lean_Meta_getLevel(v_type_4477_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; uint8_t v___x_4482_; lean_object* v___x_4483_; lean_object* v___f_4484_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___x_4561_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref_known(v___x_4480_, 1);
v___x_4482_ = 0;
lean_inc_ref_n(v_type_4477_, 2);
lean_inc_n(v_declName_4476_, 2);
v___x_4483_ = l_Lean_mkLambda(v_declName_4476_, v___x_4482_, v_type_4477_, v_body_4479_);
lean_inc_ref(v_value_4478_);
lean_inc_ref_n(v___x_4483_, 2);
v___f_4484_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4484_, 0, v___x_4483_);
lean_closure_set(v___f_4484_, 1, v_declName_4476_);
lean_closure_set(v___f_4484_, 2, v_type_4477_);
lean_closure_set(v___f_4484_, 3, v_value_4478_);
lean_closure_set(v___f_4484_, 4, v_rhs_4470_);
v___x_4561_ = l_Lean_Meta_isTypeCorrect(v___x_4483_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v_a_4562_; uint8_t v___x_4563_; 
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_a_4562_);
lean_dec_ref_known(v___x_4561_, 1);
v___x_4563_ = lean_unbox(v_a_4562_);
lean_dec(v_a_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec_ref(v___f_4484_);
lean_dec_ref(v___x_4483_);
lean_dec(v_a_4481_);
lean_dec_ref(v_value_4478_);
lean_dec_ref(v_type_4477_);
lean_dec(v_declName_4476_);
lean_dec(v_mvarId_4468_);
v___x_4564_ = lean_obj_once(&l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3, &l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__3);
v___x_4565_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4564_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_);
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4565_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4565_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
else
{
v___y_4486_ = v_a_4471_;
v___y_4487_ = v_a_4472_;
v___y_4488_ = v_a_4473_;
v___y_4489_ = v_a_4474_;
goto v___jp_4485_;
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_dec_ref(v___f_4484_);
lean_dec_ref(v___x_4483_);
lean_dec(v_a_4481_);
lean_dec_ref(v_value_4478_);
lean_dec_ref(v_type_4477_);
lean_dec(v_declName_4476_);
lean_dec(v_mvarId_4468_);
v_a_4574_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4561_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4561_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
v___jp_4485_:
{
lean_object* v___x_4490_; 
lean_inc_ref(v_type_4477_);
lean_inc(v_declName_4476_);
v___x_4490_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4476_, v_type_4477_, v___f_4484_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; lean_object* v_snd_4492_; lean_object* v_fst_4493_; lean_object* v_fst_4494_; lean_object* v_snd_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4552_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
v_snd_4492_ = lean_ctor_get(v_a_4491_, 1);
lean_inc(v_snd_4492_);
v_fst_4493_ = lean_ctor_get(v_a_4491_, 0);
lean_inc(v_fst_4493_);
lean_dec(v_a_4491_);
v_fst_4494_ = lean_ctor_get(v_snd_4492_, 0);
v_snd_4495_ = lean_ctor_get(v_snd_4492_, 1);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_snd_4492_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4497_ = v_snd_4492_;
v_isShared_4498_ = v_isSharedCheck_4552_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_snd_4495_);
lean_inc(v_fst_4494_);
lean_dec(v_snd_4492_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4552_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___f_4499_; lean_object* v___x_4500_; 
lean_inc(v_snd_4495_);
lean_inc_ref(v___x_4483_);
v___f_4499_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___lam__1___boxed), 8, 2);
lean_closure_set(v___f_4499_, 0, v___x_4483_);
lean_closure_set(v___f_4499_, 1, v_snd_4495_);
lean_inc_ref(v_type_4477_);
v___x_4500_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0___redArg(v_declName_4476_, v_type_4477_, v___f_4499_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v_fst_4502_; lean_object* v_snd_4503_; lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4543_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4500_, 1);
v_fst_4502_ = lean_ctor_get(v_a_4501_, 0);
v_snd_4503_ = lean_ctor_get(v_a_4501_, 1);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_a_4501_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4505_ = v_a_4501_;
v_isShared_4506_ = v_isSharedCheck_4543_;
goto v_resetjp_4504_;
}
else
{
lean_inc(v_snd_4503_);
lean_inc(v_fst_4502_);
lean_dec(v_a_4501_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4543_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4507_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___closed__1));
v___x_4508_ = lean_box(0);
if (v_isShared_4506_ == 0)
{
lean_ctor_set_tag(v___x_4505_, 1);
lean_ctor_set(v___x_4505_, 1, v___x_4508_);
lean_ctor_set(v___x_4505_, 0, v_fst_4494_);
v___x_4510_ = v___x_4505_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_fst_4494_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v___x_4508_);
v___x_4510_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4512_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 1);
lean_ctor_set(v___x_4497_, 1, v___x_4510_);
lean_ctor_set(v___x_4497_, 0, v_a_4481_);
v___x_4512_ = v___x_4497_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_a_4481_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4539_; 
v___x_4513_ = l_Lean_mkConst(v___x_4507_, v___x_4512_);
v___x_4514_ = l_Lean_mkApp6(v___x_4513_, v_type_4477_, v_fst_4493_, v___x_4483_, v_snd_4495_, v_value_4478_, v_fst_4502_);
v___x_4515_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4468_, v___x_4514_, v___y_4487_);
v_isSharedCheck_4539_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; 
v_unused_4540_ = lean_ctor_get(v___x_4515_, 0);
lean_dec(v_unused_4540_);
v___x_4517_ = v___x_4515_;
v_isShared_4518_ = v_isSharedCheck_4539_;
goto v_resetjp_4516_;
}
else
{
lean_dec(v___x_4515_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4539_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4519_; 
v___x_4519_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4503_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4530_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4522_ = v___x_4519_;
v_isShared_4523_ = v_isSharedCheck_4530_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4519_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4530_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4518_ == 0)
{
lean_ctor_set_tag(v___x_4517_, 1);
lean_ctor_set(v___x_4517_, 0, v_a_4520_);
v___x_4525_ = v___x_4517_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4527_; 
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4525_);
v___x_4527_ = v___x_4522_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4525_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_del_object(v___x_4517_);
v_a_4531_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4519_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4519_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
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
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_del_object(v___x_4497_);
lean_dec(v_snd_4495_);
lean_dec(v_fst_4494_);
lean_dec(v_fst_4493_);
lean_dec_ref(v___x_4483_);
lean_dec(v_a_4481_);
lean_dec_ref(v_value_4478_);
lean_dec_ref(v_type_4477_);
lean_dec(v_mvarId_4468_);
v_a_4544_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4500_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4500_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec_ref(v___x_4483_);
lean_dec(v_a_4481_);
lean_dec_ref(v_value_4478_);
lean_dec_ref(v_type_4477_);
lean_dec(v_declName_4476_);
lean_dec(v_mvarId_4468_);
v_a_4553_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4490_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4490_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
else
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4589_; 
lean_dec_ref(v_body_4479_);
lean_dec_ref(v_value_4478_);
lean_dec_ref(v_type_4477_);
lean_dec(v_declName_4476_);
lean_dec_ref(v_rhs_4470_);
lean_dec(v_mvarId_4468_);
v_a_4582_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4584_ = v___x_4480_;
v_isShared_4585_ = v_isSharedCheck_4589_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4480_);
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
else
{
lean_object* v___x_4590_; lean_object* v___x_4591_; 
lean_dec_ref(v_rhs_4470_);
lean_dec_ref(v_lhs_4469_);
lean_dec(v_mvarId_4468_);
v___x_4590_ = lean_box(0);
v___x_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4590_);
return v___x_4591_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4468_ = stack[0].m_obj;
lean_object* v_lhs_4469_ = stack[1].m_obj;
lean_object* v_rhs_4470_ = stack[2].m_obj;
lean_object* v_a_4471_ = stack[3].m_obj;
lean_object* v_a_4472_ = stack[4].m_obj;
lean_object* v_a_4473_ = stack[5].m_obj;
lean_object* v_a_4474_ = stack[6].m_obj;
lean_object* v_res_4592_;
v_res_4592_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4468_, v_lhs_4469_, v_rhs_4470_, v_a_4471_, v_a_4472_, v_a_4473_, v_a_4474_);
stack->m_obj
 = v_res_4592_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f___boxed(lean_object* v_mvarId_4593_, lean_object* v_lhs_4594_, lean_object* v_rhs_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4593_, v_lhs_4594_, v_rhs_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
return v_res_4601_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(lean_object* v_body_4603_, lean_object* v_snd_4604_, lean_object* v_b_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v___x_4611_ = lean_expr_instantiate1(v_body_4603_, v_b_4605_);
v___x_4612_ = lean_box(0);
v___x_4613_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(v___x_4611_, v___x_4612_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v_fst_4615_; lean_object* v_snd_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4678_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_a_4614_);
lean_dec_ref_known(v___x_4613_, 1);
v_fst_4615_ = lean_ctor_get(v_a_4614_, 0);
v_snd_4616_ = lean_ctor_get(v_a_4614_, 1);
v_isSharedCheck_4678_ = !lean_is_exclusive(v_a_4614_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4618_ = v_a_4614_;
v_isShared_4619_ = v_isSharedCheck_4678_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_snd_4616_);
lean_inc(v_fst_4615_);
lean_dec(v_a_4614_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4678_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; uint8_t v___x_4624_; uint8_t v___x_4625_; lean_object* v___x_4626_; 
v___x_4620_ = lean_unsigned_to_nat(1u);
v___x_4621_ = lean_mk_empty_array_with_capacity(v___x_4620_);
v___x_4622_ = lean_array_push(v___x_4621_, v_b_4605_);
v___x_4623_ = 0;
v___x_4624_ = 1;
v___x_4625_ = 1;
lean_inc(v_fst_4615_);
v___x_4626_ = l_Lean_Meta_mkLambdaFVars(v___x_4622_, v_fst_4615_, v___x_4623_, v___x_4624_, v___x_4623_, v___x_4624_, v___x_4625_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4628_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
lean_inc(v_a_4627_);
lean_dec_ref_known(v___x_4626_, 1);
lean_inc(v_snd_4616_);
v___x_4628_ = l_Lean_Meta_mkLambdaFVars(v___x_4622_, v_snd_4616_, v___x_4623_, v___x_4624_, v___x_4623_, v___x_4624_, v___x_4625_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v___x_4630_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc(v_a_4629_);
lean_dec_ref_known(v___x_4628_, 1);
v___x_4630_ = l_Lean_Meta_mkForallFVars(v___x_4622_, v_fst_4615_, v___x_4623_, v___x_4624_, v___x_4624_, v___x_4625_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
lean_dec_ref(v___x_4622_);
if (lean_obj_tag(v___x_4630_) == 0)
{
lean_object* v_a_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; 
v_a_4631_ = lean_ctor_get(v___x_4630_, 0);
lean_inc(v_a_4631_);
lean_dec_ref_known(v___x_4630_, 1);
v___x_4632_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_4633_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_resolveRhs(v___x_4632_, v_snd_4604_, v_a_4631_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_object* v___x_4635_; uint8_t v_isShared_4636_; uint8_t v_isSharedCheck_4644_; 
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4644_ == 0)
{
lean_object* v_unused_4645_; 
v_unused_4645_ = lean_ctor_get(v___x_4633_, 0);
lean_dec(v_unused_4645_);
v___x_4635_ = v___x_4633_;
v_isShared_4636_ = v_isSharedCheck_4644_;
goto v_resetjp_4634_;
}
else
{
lean_dec(v___x_4633_);
v___x_4635_ = lean_box(0);
v_isShared_4636_ = v_isSharedCheck_4644_;
goto v_resetjp_4634_;
}
v_resetjp_4634_:
{
lean_object* v___x_4638_; 
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v_a_4629_);
v___x_4638_ = v___x_4618_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4629_);
lean_ctor_set(v_reuseFailAlloc_4643_, 1, v_snd_4616_);
v___x_4638_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4637_;
}
v_reusejp_4637_:
{
lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4639_, 0, v_a_4627_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
if (v_isShared_4636_ == 0)
{
lean_ctor_set(v___x_4635_, 0, v___x_4639_);
v___x_4641_ = v___x_4635_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4639_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
else
{
lean_object* v_a_4646_; lean_object* v___x_4648_; uint8_t v_isShared_4649_; uint8_t v_isSharedCheck_4653_; 
lean_dec(v_a_4629_);
lean_dec(v_a_4627_);
lean_del_object(v___x_4618_);
lean_dec(v_snd_4616_);
v_a_4646_ = lean_ctor_get(v___x_4633_, 0);
v_isSharedCheck_4653_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4648_ = v___x_4633_;
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
else
{
lean_inc(v_a_4646_);
lean_dec(v___x_4633_);
v___x_4648_ = lean_box(0);
v_isShared_4649_ = v_isSharedCheck_4653_;
goto v_resetjp_4647_;
}
v_resetjp_4647_:
{
lean_object* v___x_4651_; 
if (v_isShared_4649_ == 0)
{
v___x_4651_ = v___x_4648_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v_a_4646_);
v___x_4651_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
return v___x_4651_;
}
}
}
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec(v_a_4629_);
lean_dec(v_a_4627_);
lean_del_object(v___x_4618_);
lean_dec(v_snd_4616_);
lean_dec_ref(v_snd_4604_);
v_a_4654_ = lean_ctor_get(v___x_4630_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4630_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4630_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec(v_a_4627_);
lean_dec_ref(v___x_4622_);
lean_del_object(v___x_4618_);
lean_dec(v_snd_4616_);
lean_dec(v_fst_4615_);
lean_dec_ref(v_snd_4604_);
v_a_4662_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4628_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4628_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
lean_dec_ref(v___x_4622_);
lean_del_object(v___x_4618_);
lean_dec(v_snd_4616_);
lean_dec(v_fst_4615_);
lean_dec_ref(v_snd_4604_);
v_a_4670_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4626_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4626_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_dec_ref(v_b_4605_);
lean_dec_ref(v_snd_4604_);
v_a_4679_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4613_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4613_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_4603_ = stack[0].m_obj;
lean_object* v_snd_4604_ = stack[1].m_obj;
lean_object* v_b_4605_ = stack[2].m_obj;
lean_object* v___y_4606_ = stack[3].m_obj;
lean_object* v___y_4607_ = stack[4].m_obj;
lean_object* v___y_4608_ = stack[5].m_obj;
lean_object* v___y_4609_ = stack[6].m_obj;
lean_object* v_res_4687_;
v_res_4687_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(v_body_4603_, v_snd_4604_, v_b_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
stack->m_obj
 = v_res_4687_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed(lean_object* v_body_4688_, lean_object* v_snd_4689_, lean_object* v_b_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0(v_body_4688_, v_snd_4689_, v_b_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec_ref(v_body_4688_);
return v_res_4696_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(lean_object* v_body_4697_, lean_object* v_snd_4698_, lean_object* v_name_4699_, uint8_t v_bi_4700_, lean_object* v_type_4701_, uint8_t v_kind_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v___f_4708_; lean_object* v___x_4709_; 
v___f_4708_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4708_, 0, v_body_4697_);
lean_closure_set(v___f_4708_, 1, v_snd_4698_);
v___x_4709_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4699_, v_bi_4700_, v_type_4701_, v___f_4708_, v_kind_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4709_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4709_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
v_a_4718_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4709_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4709_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_4697_ = stack[0].m_obj;
lean_object* v_snd_4698_ = stack[1].m_obj;
lean_object* v_name_4699_ = stack[2].m_obj;
uint8_t v_bi_4700_ = stack[3].m_num;
lean_object* v_type_4701_ = stack[4].m_obj;
uint8_t v_kind_4702_ = stack[5].m_num;
lean_object* v___y_4703_ = stack[6].m_obj;
lean_object* v___y_4704_ = stack[7].m_obj;
lean_object* v___y_4705_ = stack[8].m_obj;
lean_object* v___y_4706_ = stack[9].m_obj;
lean_object* v_res_4726_;
v_res_4726_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4697_, v_snd_4698_, v_name_4699_, v_bi_4700_, v_type_4701_, v_kind_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
stack->m_obj
 = v_res_4726_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___boxed(lean_object* v_body_4727_, lean_object* v_snd_4728_, lean_object* v_name_4729_, lean_object* v_bi_4730_, lean_object* v_type_4731_, lean_object* v_kind_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
uint8_t v_bi_boxed_4738_; uint8_t v_kind_boxed_4739_; lean_object* v_res_4740_; 
v_bi_boxed_4738_ = lean_unbox(v_bi_4730_);
v_kind_boxed_4739_ = lean_unbox(v_kind_4732_);
v_res_4740_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4727_, v_snd_4728_, v_name_4729_, v_bi_boxed_4738_, v_type_4731_, v_kind_boxed_4739_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
return v_res_4740_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__0));
v___x_4743_ = l_Lean_stringToMessageData(v___x_4742_);
return v___x_4743_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__6));
v___x_4752_ = l_Lean_stringToMessageData(v___x_4751_);
return v___x_4752_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9(void){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__8));
v___x_4755_ = l_Lean_stringToMessageData(v___x_4754_);
return v___x_4755_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(lean_object* v_mvarId_4756_, lean_object* v_userName_x3f_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4771_; lean_object* v___y_4772_; uint8_t v___y_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; lean_object* v___y_4777_; lean_object* v___x_4830_; 
lean_inc(v_mvarId_4756_);
v___x_4830_ = l_Lean_Elab_Tactic_Conv_getLhsRhsCore(v_mvarId_4756_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v_fst_4832_; lean_object* v_snd_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4966_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref_known(v___x_4830_, 1);
v_fst_4832_ = lean_ctor_get(v_a_4831_, 0);
v_snd_4833_ = lean_ctor_get(v_a_4831_, 1);
v_isSharedCheck_4966_ = !lean_is_exclusive(v_a_4831_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4835_ = v_a_4831_;
v_isShared_4836_ = v_isSharedCheck_4966_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_snd_4833_);
lean_inc(v_fst_4832_);
lean_dec(v_a_4831_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4966_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4837_; lean_object* v_a_4838_; lean_object* v___x_4839_; 
v___x_4837_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Conv_congr_spec__0___redArg(v_fst_4832_, v___y_4759_);
v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
lean_inc(v_a_4838_);
lean_dec_ref(v___x_4837_);
v___x_4839_ = l_Lean_Expr_cleanupAnnotations(v_a_4838_);
if (lean_obj_tag(v___x_4839_) == 7)
{
lean_object* v_binderName_4840_; lean_object* v_binderType_4841_; lean_object* v_body_4842_; uint8_t v_binderInfo_4843_; lean_object* v___x_4844_; 
lean_del_object(v___x_4835_);
v_binderName_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_binderName_4840_);
v_binderType_4841_ = lean_ctor_get(v___x_4839_, 1);
lean_inc_ref_n(v_binderType_4841_, 2);
v_body_4842_ = lean_ctor_get(v___x_4839_, 2);
lean_inc_ref(v_body_4842_);
v_binderInfo_4843_ = lean_ctor_get_uint8(v___x_4839_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_4839_, 3);
v___x_4844_ = l_Lean_Meta_getLevel(v_binderType_4841_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4846_; lean_object* v_userName_4848_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v___y_4851_; lean_object* v___y_4852_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc(v_a_4845_);
lean_dec_ref_known(v___x_4844_, 1);
lean_inc_ref(v_body_4842_);
lean_inc_ref(v_binderType_4841_);
lean_inc(v_binderName_4840_);
v___x_4846_ = l_Lean_Expr_lam___override(v_binderName_4840_, v_binderType_4841_, v_body_4842_, v_binderInfo_4843_);
if (lean_obj_tag(v_userName_x3f_4757_) == 1)
{
lean_object* v_val_4889_; 
lean_dec(v_binderName_4840_);
v_val_4889_ = lean_ctor_get(v_userName_x3f_4757_, 0);
lean_inc(v_val_4889_);
lean_dec_ref_known(v_userName_x3f_4757_, 1);
v_userName_4848_ = v_val_4889_;
v___y_4849_ = v___y_4758_;
v___y_4850_ = v___y_4759_;
v___y_4851_ = v___y_4760_;
v___y_4852_ = v___y_4761_;
goto v___jp_4847_;
}
else
{
lean_object* v___x_4890_; 
lean_dec(v_userName_x3f_4757_);
v___x_4890_ = l_Lean_Meta_mkFreshBinderNameForTactic___redArg(v_binderName_4840_, v___y_4758_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___x_4890_, 1);
v_userName_4848_ = v_a_4891_;
v___y_4849_ = v___y_4758_;
v___y_4850_ = v___y_4759_;
v___y_4851_ = v___y_4760_;
v___y_4852_ = v___y_4761_;
goto v___jp_4847_;
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec_ref(v___x_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_body_4842_);
lean_dec_ref(v_binderType_4841_);
lean_dec(v_snd_4833_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_mvarId_4756_);
v_a_4892_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4890_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4890_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
v___jp_4847_:
{
uint8_t v___x_4853_; lean_object* v___x_4854_; 
v___x_4853_ = 0;
lean_inc_ref(v_binderType_4841_);
v___x_4854_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0(v_body_4842_, v_snd_4833_, v_userName_4848_, v_binderInfo_4843_, v_binderType_4841_, v___x_4853_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec_ref(v___y_4849_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v_snd_4856_; lean_object* v_fst_4857_; lean_object* v_fst_4858_; lean_object* v_snd_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4880_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4855_);
lean_dec_ref_known(v___x_4854_, 1);
v_snd_4856_ = lean_ctor_get(v_a_4855_, 1);
lean_inc(v_snd_4856_);
v_fst_4857_ = lean_ctor_get(v_a_4855_, 0);
lean_inc(v_fst_4857_);
lean_dec(v_a_4855_);
v_fst_4858_ = lean_ctor_get(v_snd_4856_, 0);
v_snd_4859_ = lean_ctor_get(v_snd_4856_, 1);
v_isSharedCheck_4880_ = !lean_is_exclusive(v_snd_4856_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4861_ = v_snd_4856_;
v_isShared_4862_ = v_isSharedCheck_4880_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_snd_4859_);
lean_inc(v_fst_4858_);
lean_dec(v_snd_4856_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4880_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__5));
v___x_4864_ = lean_box(0);
if (v_isShared_4862_ == 0)
{
lean_ctor_set_tag(v___x_4861_, 1);
lean_ctor_set(v___x_4861_, 1, v___x_4864_);
lean_ctor_set(v___x_4861_, 0, v_a_4845_);
v___x_4866_ = v___x_4861_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4845_);
lean_ctor_set(v_reuseFailAlloc_4879_, 1, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4877_; 
v___x_4867_ = l_Lean_mkConst(v___x_4863_, v___x_4866_);
v___x_4868_ = l_Lean_mkApp4(v___x_4867_, v_binderType_4841_, v___x_4846_, v_fst_4857_, v_fst_4858_);
v___x_4869_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_congr_spec__1___redArg(v_mvarId_4756_, v___x_4868_, v___y_4850_);
lean_dec(v___y_4850_);
v_isSharedCheck_4877_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4877_ == 0)
{
lean_object* v_unused_4878_; 
v_unused_4878_ = lean_ctor_get(v___x_4869_, 0);
lean_dec(v_unused_4878_);
v___x_4871_ = v___x_4869_;
v_isShared_4872_ = v_isSharedCheck_4877_;
goto v_resetjp_4870_;
}
else
{
lean_dec(v___x_4869_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4877_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4873_; lean_object* v___x_4875_; 
v___x_4873_ = l_Lean_Expr_mvarId_x21(v_snd_4859_);
lean_dec(v_snd_4859_);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4873_);
v___x_4875_ = v___x_4871_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
}
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
lean_dec(v___y_4850_);
lean_dec_ref(v___x_4846_);
lean_dec(v_a_4845_);
lean_dec_ref(v_binderType_4841_);
lean_dec(v_mvarId_4756_);
v_a_4881_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4854_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4854_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
}
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
lean_dec_ref(v_body_4842_);
lean_dec_ref(v_binderType_4841_);
lean_dec(v_binderName_4840_);
lean_dec(v_snd_4833_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v_a_4900_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4844_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4844_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
else
{
lean_object* v___x_4908_; 
lean_inc_ref(v___x_4839_);
lean_inc(v_mvarId_4756_);
v___x_4908_ = l_Lean_Elab_Tactic_Conv_extLetBodyCongr_x3f(v_mvarId_4756_, v___x_4839_, v_snd_4833_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4908_) == 0)
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4957_; 
v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4911_ = v___x_4908_;
v_isShared_4912_ = v_isSharedCheck_4957_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4908_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4957_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
if (lean_obj_tag(v_a_4909_) == 1)
{
lean_object* v_val_4913_; lean_object* v___x_4915_; 
lean_dec_ref(v___x_4839_);
lean_del_object(v___x_4835_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v_val_4913_ = lean_ctor_get(v_a_4909_, 0);
lean_inc(v_val_4913_);
lean_dec_ref_known(v_a_4909_, 1);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 0, v_val_4913_);
v___x_4915_ = v___x_4911_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_val_4913_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
else
{
lean_object* v___x_4917_; 
lean_del_object(v___x_4911_);
lean_dec(v_a_4909_);
lean_inc(v___y_4761_);
lean_inc_ref(v___y_4760_);
lean_inc(v___y_4759_);
lean_inc_ref(v___y_4758_);
lean_inc_ref(v___x_4839_);
v___x_4917_ = lean_infer_type(v___x_4839_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4917_) == 0)
{
lean_object* v_a_4918_; lean_object* v___x_4919_; 
v_a_4918_ = lean_ctor_get(v___x_4917_, 0);
lean_inc(v_a_4918_);
lean_dec_ref_known(v___x_4917_, 1);
v___x_4919_ = l_Lean_Meta_whnfD(v_a_4918_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; uint8_t v___x_4921_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
lean_inc(v_a_4920_);
lean_dec_ref_known(v___x_4919_, 1);
v___x_4921_ = l_Lean_Expr_isForall(v_a_4920_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4926_; 
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v___x_4922_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__7);
v___x_4923_ = l_Lean_MessageData_ofExpr(v___x_4839_);
v___x_4924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__9);
if (v_isShared_4836_ == 0)
{
lean_ctor_set_tag(v___x_4835_, 7);
lean_ctor_set(v___x_4835_, 1, v___x_4924_);
lean_ctor_set(v___x_4835_, 0, v___x_4923_);
v___x_4926_ = v___x_4835_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4923_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v___x_4924_);
v___x_4926_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
v___x_4927_ = l_Lean_MessageData_ofExpr(v_a_4920_);
v___x_4928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4926_);
lean_ctor_set(v___x_4928_, 1, v___x_4927_);
v___x_4929_ = l_Lean_indentD(v___x_4928_);
v___x_4930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4922_);
lean_ctor_set(v___x_4930_, 1, v___x_4929_);
v___x_4931_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4930_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4931_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4931_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
else
{
lean_dec(v_a_4920_);
lean_dec_ref(v___x_4839_);
lean_del_object(v___x_4835_);
goto v___jp_4791_;
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec_ref(v___x_4839_);
lean_del_object(v___x_4835_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v_a_4941_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4919_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4919_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec_ref(v___x_4839_);
lean_del_object(v___x_4835_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v_a_4949_ = lean_ctor_get(v___x_4917_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4917_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4917_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
}
}
else
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4965_; 
lean_dec_ref(v___x_4839_);
lean_del_object(v___x_4835_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v_a_4958_ = lean_ctor_get(v___x_4908_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4908_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4960_ = v___x_4908_;
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4908_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4965_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4963_; 
if (v_isShared_4961_ == 0)
{
v___x_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4958_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
}
}
else
{
lean_object* v_a_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4974_; 
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v_a_4967_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4974_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4974_ == 0)
{
v___x_4969_ = v___x_4830_;
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_a_4967_);
lean_dec(v___x_4830_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4974_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4972_; 
if (v_isShared_4970_ == 0)
{
v___x_4972_ = v___x_4969_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v_a_4967_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
v___jp_4763_:
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4768_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__1);
v___x_4769_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies_spec__0___redArg(v___x_4768_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
return v___x_4769_;
}
v___jp_4770_:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4778_ = lean_unsigned_to_nat(1u);
v___x_4779_ = l_Lean_Meta_introNCore(v___y_4774_, v___x_4778_, v___y_4777_, v___y_4773_, v___y_4773_, v___y_4771_, v___y_4776_, v___y_4772_, v___y_4775_);
if (lean_obj_tag(v___x_4779_) == 0)
{
lean_object* v_a_4780_; lean_object* v_snd_4781_; lean_object* v___x_4782_; 
v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc(v_a_4780_);
lean_dec_ref_known(v___x_4779_, 1);
v_snd_4781_ = lean_ctor_get(v_a_4780_, 1);
lean_inc(v_snd_4781_);
lean_dec(v_a_4780_);
v___x_4782_ = l_Lean_Elab_Tactic_Conv_markAsConvGoal(v_snd_4781_, v___y_4771_, v___y_4776_, v___y_4772_, v___y_4775_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4772_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4771_);
return v___x_4782_;
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_dec(v___y_4776_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4772_);
lean_dec_ref(v___y_4771_);
v_a_4783_ = lean_ctor_get(v___x_4779_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4779_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4779_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4779_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
v___jp_4791_:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___closed__3));
v___x_4793_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_4792_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; uint8_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4793_, 1);
v___x_4795_ = 0;
v___x_4796_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_congrImplies___closed__4));
v___x_4797_ = lean_box(0);
v___x_4798_ = l_Lean_MVarId_apply(v_mvarId_4756_, v_a_4794_, v___x_4796_, v___x_4797_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
if (lean_obj_tag(v_a_4799_) == 1)
{
lean_object* v_tail_4800_; 
v_tail_4800_ = lean_ctor_get(v_a_4799_, 1);
if (lean_obj_tag(v_tail_4800_) == 0)
{
if (lean_obj_tag(v_userName_x3f_4757_) == 1)
{
lean_object* v_head_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4810_; 
v_head_4801_ = lean_ctor_get(v_a_4799_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v_a_4799_);
if (v_isSharedCheck_4810_ == 0)
{
lean_object* v_unused_4811_; 
v_unused_4811_ = lean_ctor_get(v_a_4799_, 1);
lean_dec(v_unused_4811_);
v___x_4803_ = v_a_4799_;
v_isShared_4804_ = v_isSharedCheck_4810_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_head_4801_);
lean_dec(v_a_4799_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4810_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v_val_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
v_val_4805_ = lean_ctor_get(v_userName_x3f_4757_, 0);
lean_inc(v_val_4805_);
lean_dec_ref_known(v_userName_x3f_4757_, 1);
v___x_4806_ = lean_box(0);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 1, v___x_4806_);
lean_ctor_set(v___x_4803_, 0, v_val_4805_);
v___x_4808_ = v___x_4803_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_val_4805_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
v___y_4771_ = v___y_4758_;
v___y_4772_ = v___y_4760_;
v___y_4773_ = v___x_4795_;
v___y_4774_ = v_head_4801_;
v___y_4775_ = v___y_4761_;
v___y_4776_ = v___y_4759_;
v___y_4777_ = v___x_4808_;
goto v___jp_4770_;
}
}
}
else
{
lean_object* v_head_4812_; lean_object* v___x_4813_; 
lean_dec(v_userName_x3f_4757_);
v_head_4812_ = lean_ctor_get(v_a_4799_, 0);
lean_inc(v_head_4812_);
lean_dec_ref_known(v_a_4799_, 2);
v___x_4813_ = lean_box(0);
v___y_4771_ = v___y_4758_;
v___y_4772_ = v___y_4760_;
v___y_4773_ = v___x_4795_;
v___y_4774_ = v_head_4812_;
v___y_4775_ = v___y_4761_;
v___y_4776_ = v___y_4759_;
v___y_4777_ = v___x_4813_;
goto v___jp_4770_;
}
}
else
{
lean_dec_ref_known(v_a_4799_, 2);
lean_dec(v_userName_x3f_4757_);
v___y_4764_ = v___y_4758_;
v___y_4765_ = v___y_4759_;
v___y_4766_ = v___y_4760_;
v___y_4767_ = v___y_4761_;
goto v___jp_4763_;
}
}
else
{
lean_dec(v_a_4799_);
lean_dec(v_userName_x3f_4757_);
v___y_4764_ = v___y_4758_;
v___y_4765_ = v___y_4759_;
v___y_4766_ = v___y_4760_;
v___y_4767_ = v___y_4761_;
goto v___jp_4763_;
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
v_a_4814_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4798_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4798_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v_userName_x3f_4757_);
lean_dec(v_mvarId_4756_);
v_a_4822_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4793_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4793_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4756_ = stack[0].m_obj;
lean_object* v_userName_x3f_4757_ = stack[1].m_obj;
lean_object* v___y_4758_ = stack[2].m_obj;
lean_object* v___y_4759_ = stack[3].m_obj;
lean_object* v___y_4760_ = stack[4].m_obj;
lean_object* v___y_4761_ = stack[5].m_obj;
lean_object* v_res_4975_;
v_res_4975_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(v_mvarId_4756_, v_userName_x3f_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
stack->m_obj
 = v_res_4975_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed(lean_object* v_mvarId_4976_, lean_object* v_userName_x3f_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0(v_mvarId_4976_, v_userName_x3f_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
return v_res_4983_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(lean_object* v_mvarId_4984_, lean_object* v_userName_x3f_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_){
_start:
{
lean_object* v___f_4991_; lean_object* v___x_4992_; 
lean_inc(v_mvarId_4984_);
v___f_4991_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4991_, 0, v_mvarId_4984_);
lean_closure_set(v___f_4991_, 1, v_userName_x3f_4985_);
v___x_4992_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_congr_spec__3___redArg(v_mvarId_4984_, v___f_4991_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_);
return v___x_4992_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4984_ = stack[0].m_obj;
lean_object* v_userName_x3f_4985_ = stack[1].m_obj;
lean_object* v_a_4986_ = stack[2].m_obj;
lean_object* v_a_4987_ = stack[3].m_obj;
lean_object* v_a_4988_ = stack[4].m_obj;
lean_object* v_a_4989_ = stack[5].m_obj;
lean_object* v_res_4993_;
v_res_4993_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_mvarId_4984_, v_userName_x3f_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_);
stack->m_obj
 = v_res_4993_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore___boxed(lean_object* v_mvarId_4994_, lean_object* v_userName_x3f_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_mvarId_4994_, v_userName_x3f_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_);
lean_dec(v_a_4999_);
lean_dec_ref(v_a_4998_);
lean_dec(v_a_4997_);
lean_dec_ref(v_a_4996_);
return v_res_5001_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(lean_object* v_userName_x3f_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v___x_5009_; 
v___x_5009_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5011_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5010_);
lean_dec_ref_known(v___x_5009_, 1);
v___x_5011_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore(v_a_5010_, v_userName_x3f_5002_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5012_);
lean_dec_ref_known(v___x_5011_, 1);
v___x_5013_ = lean_box(0);
v___x_5014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5014_, 0, v_a_5012_);
lean_ctor_set(v___x_5014_, 1, v___x_5013_);
v___x_5015_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5014_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
return v___x_5015_;
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
v_a_5016_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_5011_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_5011_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
else
{
lean_object* v_a_5024_; lean_object* v___x_5026_; uint8_t v_isShared_5027_; uint8_t v_isSharedCheck_5031_; 
lean_dec(v_userName_x3f_5002_);
v_a_5024_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5031_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5031_ == 0)
{
v___x_5026_ = v___x_5009_;
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
else
{
lean_inc(v_a_5024_);
lean_dec(v___x_5009_);
v___x_5026_ = lean_box(0);
v_isShared_5027_ = v_isSharedCheck_5031_;
goto v_resetjp_5025_;
}
v_resetjp_5025_:
{
lean_object* v___x_5029_; 
if (v_isShared_5027_ == 0)
{
v___x_5029_ = v___x_5026_;
goto v_reusejp_5028_;
}
else
{
lean_object* v_reuseFailAlloc_5030_; 
v_reuseFailAlloc_5030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5030_, 0, v_a_5024_);
v___x_5029_ = v_reuseFailAlloc_5030_;
goto v_reusejp_5028_;
}
v_reusejp_5028_:
{
return v___x_5029_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_userName_x3f_5002_ = stack[0].m_obj;
lean_object* v_a_5003_ = stack[1].m_obj;
lean_object* v_a_5004_ = stack[2].m_obj;
lean_object* v_a_5005_ = stack[3].m_obj;
lean_object* v_a_5006_ = stack[4].m_obj;
lean_object* v_a_5007_ = stack[5].m_obj;
lean_object* v_res_5032_;
v_res_5032_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_);
stack->m_obj
 = v_res_5032_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg___boxed(lean_object* v_userName_x3f_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
lean_dec(v_a_5034_);
return v_res_5040_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(lean_object* v_userName_x3f_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_){
_start:
{
lean_object* v___x_5051_; 
v___x_5051_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v_userName_x3f_5041_, v_a_5043_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
return v___x_5051_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext_0interp(lean_interpreter_value* stack)
{
lean_object* v_userName_x3f_5041_ = stack[0].m_obj;
lean_object* v_a_5042_ = stack[1].m_obj;
lean_object* v_a_5043_ = stack[2].m_obj;
lean_object* v_a_5044_ = stack[3].m_obj;
lean_object* v_a_5045_ = stack[4].m_obj;
lean_object* v_a_5046_ = stack[5].m_obj;
lean_object* v_a_5047_ = stack[6].m_obj;
lean_object* v_a_5048_ = stack[7].m_obj;
lean_object* v_a_5049_ = stack[8].m_obj;
lean_object* v_res_5052_;
v_res_5052_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(v_userName_x3f_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
stack->m_obj
 = v_res_5052_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___boxed(lean_object* v_userName_x3f_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext(v_userName_x3f_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_);
lean_dec(v_a_5061_);
lean_dec_ref(v_a_5060_);
lean_dec(v_a_5059_);
lean_dec_ref(v_a_5058_);
lean_dec(v_a_5057_);
lean_dec_ref(v_a_5056_);
lean_dec(v_a_5055_);
lean_dec_ref(v_a_5054_);
return v_res_5063_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(lean_object* v_as_5071_, size_t v_sz_5072_, size_t v_i_5073_, lean_object* v_b_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
uint8_t v___x_5081_; 
v___x_5081_ = lean_usize_dec_lt(v_i_5073_, v_sz_5072_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; 
v___x_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5082_, 0, v_b_5074_);
return v___x_5082_;
}
else
{
lean_object* v___x_5083_; lean_object* v_a_5084_; lean_object* v___y_5086_; lean_object* v___x_5099_; uint8_t v___x_5100_; 
v___x_5083_ = lean_box(0);
v_a_5084_ = lean_array_uget_borrowed(v_as_5071_, v_i_5073_);
v___x_5099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__1));
lean_inc(v_a_5084_);
v___x_5100_ = l_Lean_Syntax_isOfKind(v_a_5084_, v___x_5099_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; 
v___x_5101_ = lean_box(0);
v___y_5086_ = v___x_5101_;
goto v___jp_5085_;
}
else
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; uint8_t v___x_5105_; 
v___x_5102_ = lean_unsigned_to_nat(0u);
v___x_5103_ = l_Lean_Syntax_getArg(v_a_5084_, v___x_5102_);
v___x_5104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__3));
lean_inc(v___x_5103_);
v___x_5105_ = l_Lean_Syntax_isOfKind(v___x_5103_, v___x_5104_);
if (v___x_5105_ == 0)
{
lean_object* v___x_5106_; 
lean_dec(v___x_5103_);
v___x_5106_ = lean_box(0);
v___y_5086_ = v___x_5106_;
goto v___jp_5085_;
}
else
{
lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5107_ = l_Lean_TSyntax_getId(v___x_5103_);
lean_dec(v___x_5103_);
v___x_5108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
v___y_5086_ = v___x_5108_;
goto v___jp_5085_;
}
}
v___jp_5085_:
{
lean_object* v_toCold_5087_; lean_object* v_currRecDepth_5088_; lean_object* v_ref_5089_; uint16_t v_optionFlags_5090_; uint8_t v_suppressElabErrors_5091_; uint8_t v_isRecordingDeps_5092_; lean_object* v_ref_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; 
v_toCold_5087_ = lean_ctor_get(v___y_5078_, 0);
v_currRecDepth_5088_ = lean_ctor_get(v___y_5078_, 1);
v_ref_5089_ = lean_ctor_get(v___y_5078_, 2);
v_optionFlags_5090_ = lean_ctor_get_uint16(v___y_5078_, sizeof(void*)*3);
v_suppressElabErrors_5091_ = lean_ctor_get_uint8(v___y_5078_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5092_ = lean_ctor_get_uint8(v___y_5078_, sizeof(void*)*3 + 3);
v_ref_5093_ = l_Lean_replaceRef(v_a_5084_, v_ref_5089_);
lean_inc(v_currRecDepth_5088_);
lean_inc_ref(v_toCold_5087_);
v___x_5094_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5094_, 0, v_toCold_5087_);
lean_ctor_set(v___x_5094_, 1, v_currRecDepth_5088_);
lean_ctor_set(v___x_5094_, 2, v_ref_5093_);
lean_ctor_set_uint16(v___x_5094_, sizeof(void*)*3, v_optionFlags_5090_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*3 + 2, v_suppressElabErrors_5091_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*3 + 3, v_isRecordingDeps_5092_);
v___x_5095_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___y_5086_, v___y_5075_, v___y_5076_, v___y_5077_, v___x_5094_, v___y_5079_);
lean_dec_ref_known(v___x_5094_, 3);
if (lean_obj_tag(v___x_5095_) == 0)
{
size_t v___x_5096_; size_t v___x_5097_; 
lean_dec_ref_known(v___x_5095_, 1);
v___x_5096_ = ((size_t)1ULL);
v___x_5097_ = lean_usize_add(v_i_5073_, v___x_5096_);
v_i_5073_ = v___x_5097_;
v_b_5074_ = v___x_5083_;
goto _start;
}
else
{
return v___x_5095_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5071_ = stack[0].m_obj;
size_t v_sz_5072_ = stack[1].m_num;
size_t v_i_5073_ = stack[2].m_num;
lean_object* v_b_5074_ = stack[3].m_obj;
lean_object* v___y_5075_ = stack[4].m_obj;
lean_object* v___y_5076_ = stack[5].m_obj;
lean_object* v___y_5077_ = stack[6].m_obj;
lean_object* v___y_5078_ = stack[7].m_obj;
lean_object* v___y_5079_ = stack[8].m_obj;
lean_object* v_res_5109_;
v_res_5109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5071_, v_sz_5072_, v_i_5073_, v_b_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
stack->m_obj
 = v_res_5109_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___boxed(lean_object* v_as_5110_, lean_object* v_sz_5111_, lean_object* v_i_5112_, lean_object* v_b_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_){
_start:
{
size_t v_sz_boxed_5120_; size_t v_i_boxed_5121_; lean_object* v_res_5122_; 
v_sz_boxed_5120_ = lean_unbox_usize(v_sz_5111_);
lean_dec(v_sz_5111_);
v_i_boxed_5121_ = lean_unbox_usize(v_i_5112_);
lean_dec(v_i_5112_);
v_res_5122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5110_, v_sz_boxed_5120_, v_i_boxed_5121_, v_b_5113_, v___y_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5115_);
lean_dec(v___y_5114_);
lean_dec_ref(v_as_5110_);
return v_res_5122_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalExt(lean_object* v_stx_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_, lean_object* v_a_5130_, lean_object* v_a_5131_){
_start:
{
lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v_ids_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; uint8_t v___x_5138_; 
v___x_5133_ = lean_unsigned_to_nat(1u);
v___x_5134_ = l_Lean_Syntax_getArg(v_stx_5123_, v___x_5133_);
v_ids_5135_ = l_Lean_Syntax_getArgs(v___x_5134_);
lean_dec(v___x_5134_);
v___x_5136_ = lean_array_get_size(v_ids_5135_);
v___x_5137_ = lean_unsigned_to_nat(0u);
v___x_5138_ = lean_nat_dec_eq(v___x_5136_, v___x_5137_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; size_t v_sz_5140_; size_t v___x_5141_; lean_object* v___x_5142_; 
v___x_5139_ = lean_box(0);
v_sz_5140_ = lean_array_size(v_ids_5135_);
v___x_5141_ = ((size_t)0ULL);
v___x_5142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_ids_5135_, v_sz_5140_, v___x_5141_, v___x_5139_, v_a_5125_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
lean_dec_ref(v_ids_5135_);
if (lean_obj_tag(v___x_5142_) == 0)
{
lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5149_; 
v_isSharedCheck_5149_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5149_ == 0)
{
lean_object* v_unused_5150_; 
v_unused_5150_ = lean_ctor_get(v___x_5142_, 0);
lean_dec(v_unused_5150_);
v___x_5144_ = v___x_5142_;
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
else
{
lean_dec(v___x_5142_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5149_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5147_; 
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 0, v___x_5139_);
v___x_5147_ = v___x_5144_;
goto v_reusejp_5146_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5139_);
v___x_5147_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5146_;
}
v_reusejp_5146_:
{
return v___x_5147_;
}
}
}
else
{
return v___x_5142_;
}
}
else
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
lean_dec_ref(v_ids_5135_);
v___x_5151_ = lean_box(0);
v___x_5152_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_ext___redArg(v___x_5151_, v_a_5125_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
return v___x_5152_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_5123_ = stack[0].m_obj;
lean_object* v_a_5124_ = stack[1].m_obj;
lean_object* v_a_5125_ = stack[2].m_obj;
lean_object* v_a_5126_ = stack[3].m_obj;
lean_object* v_a_5127_ = stack[4].m_obj;
lean_object* v_a_5128_ = stack[5].m_obj;
lean_object* v_a_5129_ = stack[6].m_obj;
lean_object* v_a_5130_ = stack[7].m_obj;
lean_object* v_a_5131_ = stack[8].m_obj;
lean_object* v_res_5153_;
v_res_5153_ = l_Lean_Elab_Tactic_Conv_evalExt(v_stx_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_, v_a_5131_);
stack->m_obj
 = v_res_5153_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalExt___boxed(lean_object* v_stx_5154_, lean_object* v_a_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Lean_Elab_Tactic_Conv_evalExt(v_stx_5154_, v_a_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_);
lean_dec(v_a_5162_);
lean_dec_ref(v_a_5161_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
lean_dec(v_a_5158_);
lean_dec_ref(v_a_5157_);
lean_dec(v_a_5156_);
lean_dec_ref(v_a_5155_);
lean_dec(v_stx_5154_);
return v_res_5164_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(lean_object* v_as_5165_, size_t v_sz_5166_, size_t v_i_5167_, lean_object* v_b_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_){
_start:
{
lean_object* v___x_5178_; 
v___x_5178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg(v_as_5165_, v_sz_5166_, v_i_5167_, v_b_5168_, v___y_5170_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
return v___x_5178_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5165_ = stack[0].m_obj;
size_t v_sz_5166_ = stack[1].m_num;
size_t v_i_5167_ = stack[2].m_num;
lean_object* v_b_5168_ = stack[3].m_obj;
lean_object* v___y_5169_ = stack[4].m_obj;
lean_object* v___y_5170_ = stack[5].m_obj;
lean_object* v___y_5171_ = stack[6].m_obj;
lean_object* v___y_5172_ = stack[7].m_obj;
lean_object* v___y_5173_ = stack[8].m_obj;
lean_object* v___y_5174_ = stack[9].m_obj;
lean_object* v___y_5175_ = stack[10].m_obj;
lean_object* v___y_5176_ = stack[11].m_obj;
lean_object* v_res_5179_;
v_res_5179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(v_as_5165_, v_sz_5166_, v_i_5167_, v_b_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
stack->m_obj
 = v_res_5179_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___boxed(lean_object* v_as_5180_, lean_object* v_sz_5181_, lean_object* v_i_5182_, lean_object* v_b_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_){
_start:
{
size_t v_sz_boxed_5193_; size_t v_i_boxed_5194_; lean_object* v_res_5195_; 
v_sz_boxed_5193_ = lean_unbox_usize(v_sz_5181_);
lean_dec(v_sz_5181_);
v_i_boxed_5194_ = lean_unbox_usize(v_i_5182_);
lean_dec(v_i_5182_);
v_res_5195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0(v_as_5180_, v_sz_boxed_5193_, v_i_boxed_5194_, v_b_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec_ref(v_as_5180_);
return v_res_5195_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1(){
_start:
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; 
v___x_5210_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__0));
v___x_5212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5213_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalExt___boxed), 10, 0);
v___x_5214_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5210_, v___x_5211_, v___x_5212_, v___x_5213_);
return v___x_5214_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5215_;
v_res_5215_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
stack->m_obj
 = v_res_5215_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___boxed(lean_object* v_a_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1();
return v_res_5217_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3(){
_start:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt__1___closed__2));
v___x_5245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___closed__6));
v___x_5246_ = l_Lean_addBuiltinDeclarationRanges(v___x_5244_, v___x_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5247_;
v_res_5247_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
stack->m_obj
 = v_res_5247_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3___boxed(lean_object* v_a_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalExt___regBuiltin_Lean_Elab_Tactic_Conv_evalExt_declRange__3();
return v_res_5249_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(lean_object* v___x_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v___x_5260_; 
v___x_5260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5250_);
return v___x_5260_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalEnter___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5250_ = stack[0].m_obj;
lean_object* v___y_5251_ = stack[1].m_obj;
lean_object* v___y_5252_ = stack[2].m_obj;
lean_object* v___y_5253_ = stack[3].m_obj;
lean_object* v___y_5254_ = stack[4].m_obj;
lean_object* v___y_5255_ = stack[5].m_obj;
lean_object* v___y_5256_ = stack[6].m_obj;
lean_object* v___y_5257_ = stack[7].m_obj;
lean_object* v___y_5258_ = stack[8].m_obj;
lean_object* v_res_5261_;
v_res_5261_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(v___x_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
stack->m_obj
 = v_res_5261_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__0___boxed(lean_object* v___x_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__0(v___x_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec(v___y_5264_);
lean_dec_ref(v___y_5263_);
return v_res_5272_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(lean_object* v_a_5273_, lean_object* v_trees_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_){
_start:
{
lean_object* v___x_5284_; 
lean_inc(v___y_5282_);
lean_inc_ref(v___y_5281_);
lean_inc(v___y_5280_);
lean_inc_ref(v___y_5279_);
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
lean_inc(v___y_5276_);
lean_inc_ref(v___y_5275_);
v___x_5284_ = lean_apply_9(v_a_5273_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, lean_box(0));
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5293_; 
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5287_ = v___x_5284_;
v_isShared_5288_ = v_isSharedCheck_5293_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5284_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5293_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5289_, 0, v_a_5285_);
lean_ctor_set(v___x_5289_, 1, v_trees_5274_);
if (v_isShared_5288_ == 0)
{
lean_ctor_set(v___x_5287_, 0, v___x_5289_);
v___x_5291_ = v___x_5287_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
else
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5301_; 
lean_dec_ref(v_trees_5274_);
v_a_5294_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5296_ = v___x_5284_;
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5284_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5299_; 
if (v_isShared_5297_ == 0)
{
v___x_5299_ = v___x_5296_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalEnter___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5273_ = stack[0].m_obj;
lean_object* v_trees_5274_ = stack[1].m_obj;
lean_object* v___y_5275_ = stack[2].m_obj;
lean_object* v___y_5276_ = stack[3].m_obj;
lean_object* v___y_5277_ = stack[4].m_obj;
lean_object* v___y_5278_ = stack[5].m_obj;
lean_object* v___y_5279_ = stack[6].m_obj;
lean_object* v___y_5280_ = stack[7].m_obj;
lean_object* v___y_5281_ = stack[8].m_obj;
lean_object* v___y_5282_ = stack[9].m_obj;
lean_object* v_res_5302_;
v_res_5302_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(v_a_5273_, v_trees_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
stack->m_obj
 = v_res_5302_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed(lean_object* v_a_5303_, lean_object* v_trees_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_){
_start:
{
lean_object* v_res_5314_; 
v_res_5314_ = l_Lean_Elab_Tactic_Conv_evalEnter___lam__1(v_a_5303_, v_trees_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v___y_5310_);
lean_dec_ref(v___y_5309_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
return v_res_5314_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(lean_object* v_a_5315_, lean_object* v_trees_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v___x_5326_; 
lean_inc(v___y_5324_);
lean_inc_ref(v___y_5323_);
lean_inc(v___y_5322_);
lean_inc_ref(v___y_5321_);
lean_inc(v___y_5320_);
lean_inc_ref(v___y_5319_);
lean_inc(v___y_5318_);
lean_inc_ref(v___y_5317_);
v___x_5326_ = lean_apply_9(v_a_5315_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, lean_box(0));
if (lean_obj_tag(v___x_5326_) == 0)
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5335_; 
v_a_5327_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5335_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5335_ == 0)
{
v___x_5329_ = v___x_5326_;
v_isShared_5330_ = v_isSharedCheck_5335_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5326_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5335_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5331_; lean_object* v___x_5333_; 
v___x_5331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5331_, 0, v_a_5327_);
lean_ctor_set(v___x_5331_, 1, v_trees_5316_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 0, v___x_5331_);
v___x_5333_ = v___x_5329_;
goto v_reusejp_5332_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5331_);
v___x_5333_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5332_;
}
v_reusejp_5332_:
{
return v___x_5333_;
}
}
}
else
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5343_; 
lean_dec_ref(v_trees_5316_);
v_a_5336_ = lean_ctor_get(v___x_5326_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5326_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5338_ = v___x_5326_;
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5326_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5343_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5341_; 
if (v_isShared_5339_ == 0)
{
v___x_5341_ = v___x_5338_;
goto v_reusejp_5340_;
}
else
{
lean_object* v_reuseFailAlloc_5342_; 
v_reuseFailAlloc_5342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5342_, 0, v_a_5336_);
v___x_5341_ = v_reuseFailAlloc_5342_;
goto v_reusejp_5340_;
}
v_reusejp_5340_:
{
return v___x_5341_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5315_ = stack[0].m_obj;
lean_object* v_trees_5316_ = stack[1].m_obj;
lean_object* v___y_5317_ = stack[2].m_obj;
lean_object* v___y_5318_ = stack[3].m_obj;
lean_object* v___y_5319_ = stack[4].m_obj;
lean_object* v___y_5320_ = stack[5].m_obj;
lean_object* v___y_5321_ = stack[6].m_obj;
lean_object* v___y_5322_ = stack[7].m_obj;
lean_object* v___y_5323_ = stack[8].m_obj;
lean_object* v___y_5324_ = stack[9].m_obj;
lean_object* v_res_5344_;
v_res_5344_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(v_a_5315_, v_trees_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
stack->m_obj
 = v_res_5344_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed(lean_object* v_a_5345_, lean_object* v_trees_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_){
_start:
{
lean_object* v_res_5356_; 
v_res_5356_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1(v_a_5345_, v_trees_5346_, v___y_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec_ref(v___y_5353_);
lean_dec(v___y_5352_);
lean_dec_ref(v___y_5351_);
lean_dec(v___y_5350_);
lean_dec_ref(v___y_5349_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
return v_res_5356_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(uint8_t v___x_5357_, lean_object* v___x_5358_, lean_object* v___x_5359_, lean_object* v___x_5360_, lean_object* v___x_5361_, lean_object* v___x_5362_, lean_object* v___x_5363_, lean_object* v___x_5364_, lean_object* v___x_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
if (v___x_5357_ == 0)
{
lean_object* v___x_5375_; 
lean_dec_ref(v___y_5372_);
lean_dec(v___x_5365_);
lean_dec_ref(v___x_5364_);
lean_dec_ref(v___x_5363_);
lean_dec_ref(v___x_5362_);
lean_dec_ref(v___x_5361_);
v___x_5375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5375_, 0, v___x_5358_);
return v___x_5375_;
}
else
{
lean_object* v_toCold_5376_; lean_object* v_currRecDepth_5377_; lean_object* v_ref_5378_; uint16_t v_optionFlags_5379_; uint8_t v_suppressElabErrors_5380_; uint8_t v_isRecordingDeps_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5411_; 
v_toCold_5376_ = lean_ctor_get(v___y_5372_, 0);
v_currRecDepth_5377_ = lean_ctor_get(v___y_5372_, 1);
v_ref_5378_ = lean_ctor_get(v___y_5372_, 2);
v_optionFlags_5379_ = lean_ctor_get_uint16(v___y_5372_, sizeof(void*)*3);
v_suppressElabErrors_5380_ = lean_ctor_get_uint8(v___y_5372_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5381_ = lean_ctor_get_uint8(v___y_5372_, sizeof(void*)*3 + 3);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___y_5372_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5383_ = v___y_5372_;
v_isShared_5384_ = v_isSharedCheck_5411_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_ref_5378_);
lean_inc(v_currRecDepth_5377_);
lean_inc(v_toCold_5376_);
lean_dec(v___y_5372_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5411_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v_ref_5385_; lean_object* v___x_5387_; 
v_ref_5385_ = l_Lean_replaceRef(v___x_5359_, v_ref_5378_);
lean_dec(v_ref_5378_);
lean_inc(v_ref_5385_);
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 2, v_ref_5385_);
v___x_5387_ = v___x_5383_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_toCold_5376_);
lean_ctor_set(v_reuseFailAlloc_5410_, 1, v_currRecDepth_5377_);
lean_ctor_set(v_reuseFailAlloc_5410_, 2, v_ref_5385_);
lean_ctor_set_uint16(v_reuseFailAlloc_5410_, sizeof(void*)*3, v_optionFlags_5379_);
lean_ctor_set_uint8(v_reuseFailAlloc_5410_, sizeof(void*)*3 + 2, v_suppressElabErrors_5380_);
lean_ctor_set_uint8(v_reuseFailAlloc_5410_, sizeof(void*)*3 + 3, v_isRecordingDeps_5381_);
v___x_5387_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; uint8_t v___x_5391_; 
v___x_5388_ = l_Lean_Syntax_getArg(v___x_5359_, v___x_5360_);
v___x_5389_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__2));
lean_inc_ref(v___x_5364_);
lean_inc_ref(v___x_5363_);
lean_inc_ref(v___x_5362_);
lean_inc_ref(v___x_5361_);
v___x_5390_ = l_Lean_Name_mkStr5(v___x_5361_, v___x_5362_, v___x_5363_, v___x_5364_, v___x_5389_);
lean_inc(v___x_5388_);
v___x_5391_ = l_Lean_Syntax_isOfKind(v___x_5388_, v___x_5390_);
lean_dec(v___x_5390_);
if (v___x_5391_ == 0)
{
lean_object* v___x_5392_; lean_object* v___x_5393_; uint8_t v___x_5394_; 
v___x_5392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Conv_evalExt_spec__0___redArg___closed__0));
lean_inc_ref(v___x_5361_);
v___x_5393_ = l_Lean_Name_mkStr2(v___x_5361_, v___x_5392_);
lean_inc(v___x_5388_);
v___x_5394_ = l_Lean_Syntax_isOfKind(v___x_5388_, v___x_5393_);
lean_dec(v___x_5393_);
if (v___x_5394_ == 0)
{
lean_object* v___x_5395_; 
lean_dec(v___x_5388_);
lean_dec_ref(v___x_5387_);
lean_dec(v_ref_5385_);
lean_dec(v___x_5365_);
lean_dec_ref(v___x_5364_);
lean_dec_ref(v___x_5363_);
lean_dec_ref(v___x_5362_);
lean_dec_ref(v___x_5361_);
v___x_5395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5395_, 0, v___x_5358_);
return v___x_5395_;
}
else
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5396_ = l_Lean_SourceInfo_fromRef(v_ref_5385_, v___x_5391_);
lean_dec(v_ref_5385_);
v___x_5397_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Conv_congrArgForall_spec__0_spec__0___at___00__private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_extCore_spec__0___lam__0___closed__0));
v___x_5398_ = l_Lean_Name_mkStr5(v___x_5361_, v___x_5362_, v___x_5363_, v___x_5364_, v___x_5397_);
lean_inc_n(v___x_5396_, 2);
v___x_5399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5399_, 0, v___x_5396_);
lean_ctor_set(v___x_5399_, 1, v___x_5397_);
v___x_5400_ = l_Lean_Syntax_node1(v___x_5396_, v___x_5365_, v___x_5388_);
v___x_5401_ = l_Lean_Syntax_node2(v___x_5396_, v___x_5398_, v___x_5399_, v___x_5400_);
v___x_5402_ = l_Lean_Elab_Tactic_evalTactic(v___x_5401_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___x_5387_, v___y_5373_);
lean_dec_ref(v___x_5387_);
return v___x_5402_;
}
}
else
{
uint8_t v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; 
lean_dec(v___x_5365_);
v___x_5403_ = 0;
v___x_5404_ = l_Lean_SourceInfo_fromRef(v_ref_5385_, v___x_5403_);
lean_dec(v_ref_5385_);
v___x_5405_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_elabArg___closed__0));
v___x_5406_ = l_Lean_Name_mkStr5(v___x_5361_, v___x_5362_, v___x_5363_, v___x_5364_, v___x_5405_);
lean_inc(v___x_5404_);
v___x_5407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5404_);
lean_ctor_set(v___x_5407_, 1, v___x_5405_);
v___x_5408_ = l_Lean_Syntax_node2(v___x_5404_, v___x_5406_, v___x_5407_, v___x_5388_);
v___x_5409_ = l_Lean_Elab_Tactic_evalTactic(v___x_5408_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___x_5387_, v___y_5373_);
lean_dec_ref(v___x_5387_);
return v___x_5409_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_5357_ = stack[0].m_num;
lean_object* v___x_5358_ = stack[1].m_obj;
lean_object* v___x_5359_ = stack[2].m_obj;
lean_object* v___x_5360_ = stack[3].m_obj;
lean_object* v___x_5361_ = stack[4].m_obj;
lean_object* v___x_5362_ = stack[5].m_obj;
lean_object* v___x_5363_ = stack[6].m_obj;
lean_object* v___x_5364_ = stack[7].m_obj;
lean_object* v___x_5365_ = stack[8].m_obj;
lean_object* v___y_5366_ = stack[9].m_obj;
lean_object* v___y_5367_ = stack[10].m_obj;
lean_object* v___y_5368_ = stack[11].m_obj;
lean_object* v___y_5369_ = stack[12].m_obj;
lean_object* v___y_5370_ = stack[13].m_obj;
lean_object* v___y_5371_ = stack[14].m_obj;
lean_object* v___y_5372_ = stack[15].m_obj;
lean_object* v___y_5373_ = stack[16].m_obj;
lean_object* v_res_5412_;
v_res_5412_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(v___x_5357_, v___x_5358_, v___x_5359_, v___x_5360_, v___x_5361_, v___x_5362_, v___x_5363_, v___x_5364_, v___x_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
stack->m_obj
 = v_res_5412_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5413_ = _args[0];
lean_object* v___x_5414_ = _args[1];
lean_object* v___x_5415_ = _args[2];
lean_object* v___x_5416_ = _args[3];
lean_object* v___x_5417_ = _args[4];
lean_object* v___x_5418_ = _args[5];
lean_object* v___x_5419_ = _args[6];
lean_object* v___x_5420_ = _args[7];
lean_object* v___x_5421_ = _args[8];
lean_object* v___y_5422_ = _args[9];
lean_object* v___y_5423_ = _args[10];
lean_object* v___y_5424_ = _args[11];
lean_object* v___y_5425_ = _args[12];
lean_object* v___y_5426_ = _args[13];
lean_object* v___y_5427_ = _args[14];
lean_object* v___y_5428_ = _args[15];
lean_object* v___y_5429_ = _args[16];
lean_object* v___y_5430_ = _args[17];
_start:
{
uint8_t v___x_15866__boxed_5431_; lean_object* v_res_5432_; 
v___x_15866__boxed_5431_ = lean_unbox(v___x_5413_);
v_res_5432_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0(v___x_15866__boxed_5431_, v___x_5414_, v___x_5415_, v___x_5416_, v___x_5417_, v___x_5418_, v___x_5419_, v___x_5420_, v___x_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
lean_dec(v___y_5429_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___x_5416_);
lean_dec(v___x_5415_);
return v_res_5432_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5433_ = lean_unsigned_to_nat(32u);
v___x_5434_ = lean_mk_empty_array_with_capacity(v___x_5433_);
v___x_5435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5435_, 0, v___x_5434_);
return v___x_5435_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5436_ = ((size_t)5ULL);
v___x_5437_ = lean_unsigned_to_nat(0u);
v___x_5438_ = lean_unsigned_to_nat(32u);
v___x_5439_ = lean_mk_empty_array_with_capacity(v___x_5438_);
v___x_5440_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__0);
v___x_5441_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5441_, 0, v___x_5440_);
lean_ctor_set(v___x_5441_, 1, v___x_5439_);
lean_ctor_set(v___x_5441_, 2, v___x_5437_);
lean_ctor_set(v___x_5441_, 3, v___x_5437_);
lean_ctor_set_usize(v___x_5441_, 4, v___x_5436_);
return v___x_5441_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(lean_object* v___y_5442_){
_start:
{
lean_object* v___x_5444_; lean_object* v_infoState_5445_; lean_object* v_trees_5446_; lean_object* v___x_5447_; lean_object* v_infoState_5448_; lean_object* v_env_5449_; lean_object* v_nextMacroScope_5450_; lean_object* v_ngen_5451_; lean_object* v_auxDeclNGen_5452_; lean_object* v_traceState_5453_; lean_object* v_cache_5454_; lean_object* v_recordedDeps_5455_; lean_object* v_messages_5456_; lean_object* v_snapshotTasks_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5478_; 
v___x_5444_ = lean_st_ref_get(v___y_5442_);
v_infoState_5445_ = lean_ctor_get(v___x_5444_, 8);
lean_inc_ref(v_infoState_5445_);
lean_dec(v___x_5444_);
v_trees_5446_ = lean_ctor_get(v_infoState_5445_, 2);
lean_inc_ref(v_trees_5446_);
lean_dec_ref(v_infoState_5445_);
v___x_5447_ = lean_st_ref_take(v___y_5442_);
v_infoState_5448_ = lean_ctor_get(v___x_5447_, 8);
v_env_5449_ = lean_ctor_get(v___x_5447_, 0);
v_nextMacroScope_5450_ = lean_ctor_get(v___x_5447_, 1);
v_ngen_5451_ = lean_ctor_get(v___x_5447_, 2);
v_auxDeclNGen_5452_ = lean_ctor_get(v___x_5447_, 3);
v_traceState_5453_ = lean_ctor_get(v___x_5447_, 4);
v_cache_5454_ = lean_ctor_get(v___x_5447_, 5);
v_recordedDeps_5455_ = lean_ctor_get(v___x_5447_, 6);
v_messages_5456_ = lean_ctor_get(v___x_5447_, 7);
v_snapshotTasks_5457_ = lean_ctor_get(v___x_5447_, 9);
v_isSharedCheck_5478_ = !lean_is_exclusive(v___x_5447_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5459_ = v___x_5447_;
v_isShared_5460_ = v_isSharedCheck_5478_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_snapshotTasks_5457_);
lean_inc(v_infoState_5448_);
lean_inc(v_messages_5456_);
lean_inc(v_recordedDeps_5455_);
lean_inc(v_cache_5454_);
lean_inc(v_traceState_5453_);
lean_inc(v_auxDeclNGen_5452_);
lean_inc(v_ngen_5451_);
lean_inc(v_nextMacroScope_5450_);
lean_inc(v_env_5449_);
lean_dec(v___x_5447_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5478_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
uint8_t v_enabled_5461_; lean_object* v_assignment_5462_; lean_object* v_lazyAssignment_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5476_; 
v_enabled_5461_ = lean_ctor_get_uint8(v_infoState_5448_, sizeof(void*)*3);
v_assignment_5462_ = lean_ctor_get(v_infoState_5448_, 0);
v_lazyAssignment_5463_ = lean_ctor_get(v_infoState_5448_, 1);
v_isSharedCheck_5476_ = !lean_is_exclusive(v_infoState_5448_);
if (v_isSharedCheck_5476_ == 0)
{
lean_object* v_unused_5477_; 
v_unused_5477_ = lean_ctor_get(v_infoState_5448_, 2);
lean_dec(v_unused_5477_);
v___x_5465_ = v_infoState_5448_;
v_isShared_5466_ = v_isSharedCheck_5476_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_lazyAssignment_5463_);
lean_inc(v_assignment_5462_);
lean_dec(v_infoState_5448_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5476_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5467_; lean_object* v___x_5469_; 
v___x_5467_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___closed__1);
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 2, v___x_5467_);
v___x_5469_ = v___x_5465_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_assignment_5462_);
lean_ctor_set(v_reuseFailAlloc_5475_, 1, v_lazyAssignment_5463_);
lean_ctor_set(v_reuseFailAlloc_5475_, 2, v___x_5467_);
lean_ctor_set_uint8(v_reuseFailAlloc_5475_, sizeof(void*)*3, v_enabled_5461_);
v___x_5469_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
lean_object* v___x_5471_; 
if (v_isShared_5460_ == 0)
{
lean_ctor_set(v___x_5459_, 8, v___x_5469_);
v___x_5471_ = v___x_5459_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_env_5449_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v_nextMacroScope_5450_);
lean_ctor_set(v_reuseFailAlloc_5474_, 2, v_ngen_5451_);
lean_ctor_set(v_reuseFailAlloc_5474_, 3, v_auxDeclNGen_5452_);
lean_ctor_set(v_reuseFailAlloc_5474_, 4, v_traceState_5453_);
lean_ctor_set(v_reuseFailAlloc_5474_, 5, v_cache_5454_);
lean_ctor_set(v_reuseFailAlloc_5474_, 6, v_recordedDeps_5455_);
lean_ctor_set(v_reuseFailAlloc_5474_, 7, v_messages_5456_);
lean_ctor_set(v_reuseFailAlloc_5474_, 8, v___x_5469_);
lean_ctor_set(v_reuseFailAlloc_5474_, 9, v_snapshotTasks_5457_);
v___x_5471_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
lean_object* v___x_5472_; lean_object* v___x_5473_; 
v___x_5472_ = lean_st_ref_put(v___y_5442_, v___x_5471_);
v___x_5473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5473_, 0, v_trees_5446_);
return v___x_5473_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5442_ = stack[0].m_obj;
lean_object* v_res_5479_;
v_res_5479_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5442_);
stack->m_obj
 = v_res_5479_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg___boxed(lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5480_);
lean_dec(v___y_5480_);
return v_res_5482_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(lean_object* v___y_5483_, lean_object* v_mkInfoTree_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v_a_5492_, lean_object* v_a_x3f_5493_){
_start:
{
lean_object* v___x_5495_; lean_object* v_infoState_5496_; lean_object* v_trees_5497_; lean_object* v___x_5498_; 
v___x_5495_ = lean_st_ref_get(v___y_5483_);
v_infoState_5496_ = lean_ctor_get(v___x_5495_, 8);
lean_inc_ref(v_infoState_5496_);
lean_dec(v___x_5495_);
v_trees_5497_ = lean_ctor_get(v_infoState_5496_, 2);
lean_inc_ref(v_trees_5497_);
lean_dec_ref(v_infoState_5496_);
lean_inc(v___y_5483_);
lean_inc_ref(v___y_5491_);
lean_inc(v___y_5490_);
lean_inc_ref(v___y_5489_);
lean_inc(v___y_5488_);
lean_inc_ref(v___y_5487_);
lean_inc(v___y_5486_);
lean_inc_ref(v___y_5485_);
v___x_5498_ = lean_apply_10(v_mkInfoTree_5484_, v_trees_5497_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5483_, lean_box(0));
if (lean_obj_tag(v___x_5498_) == 0)
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5538_; 
v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5501_ = v___x_5498_;
v_isShared_5502_ = v_isSharedCheck_5538_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5498_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5538_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5503_; lean_object* v_infoState_5504_; lean_object* v_env_5505_; lean_object* v_nextMacroScope_5506_; lean_object* v_ngen_5507_; lean_object* v_auxDeclNGen_5508_; lean_object* v_traceState_5509_; lean_object* v_cache_5510_; lean_object* v_recordedDeps_5511_; lean_object* v_messages_5512_; lean_object* v_snapshotTasks_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5537_; 
v___x_5503_ = lean_st_ref_take(v___y_5483_);
v_infoState_5504_ = lean_ctor_get(v___x_5503_, 8);
v_env_5505_ = lean_ctor_get(v___x_5503_, 0);
v_nextMacroScope_5506_ = lean_ctor_get(v___x_5503_, 1);
v_ngen_5507_ = lean_ctor_get(v___x_5503_, 2);
v_auxDeclNGen_5508_ = lean_ctor_get(v___x_5503_, 3);
v_traceState_5509_ = lean_ctor_get(v___x_5503_, 4);
v_cache_5510_ = lean_ctor_get(v___x_5503_, 5);
v_recordedDeps_5511_ = lean_ctor_get(v___x_5503_, 6);
v_messages_5512_ = lean_ctor_get(v___x_5503_, 7);
v_snapshotTasks_5513_ = lean_ctor_get(v___x_5503_, 9);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5503_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5515_ = v___x_5503_;
v_isShared_5516_ = v_isSharedCheck_5537_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_snapshotTasks_5513_);
lean_inc(v_infoState_5504_);
lean_inc(v_messages_5512_);
lean_inc(v_recordedDeps_5511_);
lean_inc(v_cache_5510_);
lean_inc(v_traceState_5509_);
lean_inc(v_auxDeclNGen_5508_);
lean_inc(v_ngen_5507_);
lean_inc(v_nextMacroScope_5506_);
lean_inc(v_env_5505_);
lean_dec(v___x_5503_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5537_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
uint8_t v_enabled_5517_; lean_object* v_assignment_5518_; lean_object* v_lazyAssignment_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5535_; 
v_enabled_5517_ = lean_ctor_get_uint8(v_infoState_5504_, sizeof(void*)*3);
v_assignment_5518_ = lean_ctor_get(v_infoState_5504_, 0);
v_lazyAssignment_5519_ = lean_ctor_get(v_infoState_5504_, 1);
v_isSharedCheck_5535_ = !lean_is_exclusive(v_infoState_5504_);
if (v_isSharedCheck_5535_ == 0)
{
lean_object* v_unused_5536_; 
v_unused_5536_ = lean_ctor_get(v_infoState_5504_, 2);
lean_dec(v_unused_5536_);
v___x_5521_ = v_infoState_5504_;
v_isShared_5522_ = v_isSharedCheck_5535_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_lazyAssignment_5519_);
lean_inc(v_assignment_5518_);
lean_dec(v_infoState_5504_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5535_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5526_; 
v___x_5523_ = lean_box(0);
v___x_5524_ = l_Lean_PersistentArray_push___redArg(v_a_5492_, v_a_5499_);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 2, v___x_5524_);
v___x_5526_ = v___x_5521_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_assignment_5518_);
lean_ctor_set(v_reuseFailAlloc_5534_, 1, v_lazyAssignment_5519_);
lean_ctor_set(v_reuseFailAlloc_5534_, 2, v___x_5524_);
lean_ctor_set_uint8(v_reuseFailAlloc_5534_, sizeof(void*)*3, v_enabled_5517_);
v___x_5526_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5528_; 
if (v_isShared_5516_ == 0)
{
lean_ctor_set(v___x_5515_, 8, v___x_5526_);
v___x_5528_ = v___x_5515_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_env_5505_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v_nextMacroScope_5506_);
lean_ctor_set(v_reuseFailAlloc_5533_, 2, v_ngen_5507_);
lean_ctor_set(v_reuseFailAlloc_5533_, 3, v_auxDeclNGen_5508_);
lean_ctor_set(v_reuseFailAlloc_5533_, 4, v_traceState_5509_);
lean_ctor_set(v_reuseFailAlloc_5533_, 5, v_cache_5510_);
lean_ctor_set(v_reuseFailAlloc_5533_, 6, v_recordedDeps_5511_);
lean_ctor_set(v_reuseFailAlloc_5533_, 7, v_messages_5512_);
lean_ctor_set(v_reuseFailAlloc_5533_, 8, v___x_5526_);
lean_ctor_set(v_reuseFailAlloc_5533_, 9, v_snapshotTasks_5513_);
v___x_5528_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
lean_object* v___x_5529_; lean_object* v___x_5531_; 
v___x_5529_ = lean_st_ref_put(v___y_5483_, v___x_5528_);
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 0, v___x_5523_);
v___x_5531_ = v___x_5501_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v___x_5523_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
lean_dec_ref(v_a_5492_);
v_a_5539_ = lean_ctor_get(v___x_5498_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5498_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5498_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5498_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5483_ = stack[0].m_obj;
lean_object* v_mkInfoTree_5484_ = stack[1].m_obj;
lean_object* v___y_5485_ = stack[2].m_obj;
lean_object* v___y_5486_ = stack[3].m_obj;
lean_object* v___y_5487_ = stack[4].m_obj;
lean_object* v___y_5488_ = stack[5].m_obj;
lean_object* v___y_5489_ = stack[6].m_obj;
lean_object* v___y_5490_ = stack[7].m_obj;
lean_object* v___y_5491_ = stack[8].m_obj;
lean_object* v_a_5492_ = stack[9].m_obj;
lean_object* v_a_x3f_5493_ = stack[10].m_obj;
lean_object* v_res_5547_;
v_res_5547_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5483_, v_mkInfoTree_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v_a_5492_, v_a_x3f_5493_);
stack->m_obj
 = v_res_5547_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0___boxed(lean_object* v___y_5548_, lean_object* v_mkInfoTree_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v_a_5557_, lean_object* v_a_x3f_5558_, lean_object* v___y_5559_){
_start:
{
lean_object* v_res_5560_; 
v_res_5560_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5548_, v_mkInfoTree_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v_a_5557_, v_a_x3f_5558_);
lean_dec(v_a_x3f_5558_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec_ref(v___y_5550_);
lean_dec(v___y_5548_);
return v_res_5560_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(lean_object* v_x_5561_, lean_object* v_mkInfoTree_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_){
_start:
{
lean_object* v___x_5572_; lean_object* v_infoState_5573_; uint8_t v_enabled_5574_; 
v___x_5572_ = lean_st_ref_get(v___y_5570_);
v_infoState_5573_ = lean_ctor_get(v___x_5572_, 8);
lean_inc_ref(v_infoState_5573_);
lean_dec(v___x_5572_);
v_enabled_5574_ = lean_ctor_get_uint8(v_infoState_5573_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5573_);
if (v_enabled_5574_ == 0)
{
lean_object* v___x_5575_; 
lean_dec_ref(v_mkInfoTree_5562_);
lean_inc(v___y_5570_);
lean_inc_ref(v___y_5569_);
lean_inc(v___y_5568_);
lean_inc_ref(v___y_5567_);
lean_inc(v___y_5566_);
lean_inc_ref(v___y_5565_);
lean_inc(v___y_5564_);
lean_inc_ref(v___y_5563_);
v___x_5575_ = lean_apply_9(v_x_5561_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, lean_box(0));
return v___x_5575_;
}
else
{
lean_object* v___x_5576_; lean_object* v_a_5577_; lean_object* v_r_5578_; 
v___x_5576_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5570_);
v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
lean_inc(v_a_5577_);
lean_dec_ref(v___x_5576_);
lean_inc(v___y_5570_);
lean_inc_ref(v___y_5569_);
lean_inc(v___y_5568_);
lean_inc_ref(v___y_5567_);
lean_inc(v___y_5566_);
lean_inc_ref(v___y_5565_);
lean_inc(v___y_5564_);
lean_inc_ref(v___y_5563_);
v_r_5578_ = lean_apply_9(v_x_5561_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_, lean_box(0));
if (lean_obj_tag(v_r_5578_) == 0)
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5603_; 
v_a_5579_ = lean_ctor_get(v_r_5578_, 0);
v_isSharedCheck_5603_ = !lean_is_exclusive(v_r_5578_);
if (v_isSharedCheck_5603_ == 0)
{
v___x_5581_ = v_r_5578_;
v_isShared_5582_ = v_isSharedCheck_5603_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v_r_5578_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5603_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5584_; 
lean_inc(v_a_5579_);
if (v_isShared_5582_ == 0)
{
lean_ctor_set_tag(v___x_5581_, 1);
v___x_5584_ = v___x_5581_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v_a_5579_);
v___x_5584_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
lean_object* v___x_5585_; 
v___x_5585_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5570_, v_mkInfoTree_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v_a_5577_, v___x_5584_);
lean_dec_ref(v___x_5584_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5592_ == 0)
{
lean_object* v_unused_5593_; 
v_unused_5593_ = lean_ctor_get(v___x_5585_, 0);
lean_dec(v_unused_5593_);
v___x_5587_ = v___x_5585_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_dec(v___x_5585_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 0, v_a_5579_);
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5579_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
else
{
lean_object* v_a_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5601_; 
lean_dec(v_a_5579_);
v_a_5594_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5596_ = v___x_5585_;
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_a_5594_);
lean_dec(v___x_5585_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5601_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v___x_5599_; 
if (v_isShared_5597_ == 0)
{
v___x_5599_ = v___x_5596_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_a_5594_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
return v___x_5599_;
}
}
}
}
}
}
else
{
lean_object* v_a_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; 
v_a_5604_ = lean_ctor_get(v_r_5578_, 0);
lean_inc(v_a_5604_);
lean_dec_ref_known(v_r_5578_, 1);
v___x_5605_ = lean_box(0);
v___x_5606_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___lam__0(v___y_5570_, v_mkInfoTree_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v_a_5577_, v___x_5605_);
if (lean_obj_tag(v___x_5606_) == 0)
{
lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5613_; 
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5606_);
if (v_isSharedCheck_5613_ == 0)
{
lean_object* v_unused_5614_; 
v_unused_5614_ = lean_ctor_get(v___x_5606_, 0);
lean_dec(v_unused_5614_);
v___x_5608_ = v___x_5606_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_dec(v___x_5606_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5611_; 
if (v_isShared_5609_ == 0)
{
lean_ctor_set_tag(v___x_5608_, 1);
lean_ctor_set(v___x_5608_, 0, v_a_5604_);
v___x_5611_ = v___x_5608_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5604_);
v___x_5611_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5610_;
}
v_reusejp_5610_:
{
return v___x_5611_;
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_dec(v_a_5604_);
v_a_5615_ = lean_ctor_get(v___x_5606_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5606_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5606_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5606_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5561_ = stack[0].m_obj;
lean_object* v_mkInfoTree_5562_ = stack[1].m_obj;
lean_object* v___y_5563_ = stack[2].m_obj;
lean_object* v___y_5564_ = stack[3].m_obj;
lean_object* v___y_5565_ = stack[4].m_obj;
lean_object* v___y_5566_ = stack[5].m_obj;
lean_object* v___y_5567_ = stack[6].m_obj;
lean_object* v___y_5568_ = stack[7].m_obj;
lean_object* v___y_5569_ = stack[8].m_obj;
lean_object* v___y_5570_ = stack[9].m_obj;
lean_object* v_res_5623_;
v_res_5623_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5561_, v_mkInfoTree_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
stack->m_obj
 = v_res_5623_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg___boxed(lean_object* v_x_5624_, lean_object* v_mkInfoTree_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_){
_start:
{
lean_object* v_res_5635_; 
v_res_5635_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5624_, v_mkInfoTree_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec(v___y_5627_);
lean_dec_ref(v___y_5626_);
return v_res_5635_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(lean_object* v_upperBound_5646_, lean_object* v_enterArgsAndSeps_5647_, lean_object* v_a_5648_, lean_object* v_b_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
uint8_t v___x_5659_; 
v___x_5659_ = lean_nat_dec_lt(v_a_5648_, v_upperBound_5646_);
if (v___x_5659_ == 0)
{
lean_object* v___x_5660_; 
lean_dec(v_a_5648_);
v___x_5660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5660_, 0, v_b_5649_);
return v___x_5660_;
}
else
{
lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___y_5669_; lean_object* v___x_5698_; lean_object* v___x_5699_; uint8_t v___x_5700_; 
v___x_5661_ = lean_unsigned_to_nat(2u);
v___x_5662_ = lean_box(0);
v___x_5663_ = lean_box(0);
v___x_5664_ = lean_unsigned_to_nat(0u);
v___x_5665_ = lean_unsigned_to_nat(1u);
v___x_5666_ = lean_nat_mul(v___x_5661_, v_a_5648_);
v___x_5667_ = lean_array_get_borrowed(v___x_5662_, v_enterArgsAndSeps_5647_, v___x_5666_);
v___x_5698_ = lean_nat_add(v___x_5666_, v___x_5665_);
lean_dec(v___x_5666_);
v___x_5699_ = lean_array_get_size(v_enterArgsAndSeps_5647_);
v___x_5700_ = lean_nat_dec_lt(v___x_5698_, v___x_5699_);
if (v___x_5700_ == 0)
{
lean_dec(v___x_5698_);
v___y_5669_ = v___x_5662_;
goto v___jp_5668_;
}
else
{
lean_object* v___x_5701_; 
v___x_5701_ = lean_array_fget_borrowed(v_enterArgsAndSeps_5647_, v___x_5698_);
lean_dec(v___x_5698_);
lean_inc(v___x_5701_);
v___y_5669_ = v___x_5701_;
goto v___jp_5668_;
}
v___jp_5668_:
{
lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; uint8_t v___x_5681_; lean_object* v___x_5682_; lean_object* v___f_5683_; lean_object* v___x_5684_; 
v___x_5670_ = lean_mk_empty_array_with_capacity(v___x_5661_);
lean_inc_n(v___x_5667_, 3);
v___x_5671_ = lean_array_push(v___x_5670_, v___x_5667_);
v___x_5672_ = lean_array_push(v___x_5671_, v___y_5669_);
v___x_5673_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5674_ = lean_box(2);
v___x_5675_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
lean_ctor_set(v___x_5675_, 1, v___x_5673_);
lean_ctor_set(v___x_5675_, 2, v___x_5672_);
v___x_5676_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__0));
v___x_5677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__1));
v___x_5678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__2));
v___x_5679_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalSkip___regBuiltin_Lean_Elab_Tactic_Conv_evalSkip__1___closed__3));
v___x_5680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__3));
v___x_5681_ = l_Lean_Syntax_isOfKind(v___x_5667_, v___x_5680_);
v___x_5682_ = lean_box(v___x_5681_);
v___f_5683_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_5683_, 0, v___x_5682_);
lean_closure_set(v___f_5683_, 1, v___x_5663_);
lean_closure_set(v___f_5683_, 2, v___x_5667_);
lean_closure_set(v___f_5683_, 3, v___x_5664_);
lean_closure_set(v___f_5683_, 4, v___x_5676_);
lean_closure_set(v___f_5683_, 5, v___x_5677_);
lean_closure_set(v___f_5683_, 6, v___x_5678_);
lean_closure_set(v___f_5683_, 7, v___x_5679_);
lean_closure_set(v___f_5683_, 8, v___x_5673_);
v___x_5684_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5675_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v_a_5685_; lean_object* v___f_5686_; lean_object* v___x_5687_; 
v_a_5685_ = lean_ctor_get(v___x_5684_, 0);
lean_inc(v_a_5685_);
lean_dec_ref_known(v___x_5684_, 1);
v___f_5686_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5686_, 0, v_a_5685_);
v___x_5687_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5683_, v___f_5686_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
if (lean_obj_tag(v___x_5687_) == 0)
{
lean_object* v___x_5688_; 
lean_dec_ref_known(v___x_5687_, 1);
v___x_5688_ = lean_nat_add(v_a_5648_, v___x_5665_);
lean_dec(v_a_5648_);
v_a_5648_ = v___x_5688_;
v_b_5649_ = v___x_5663_;
goto _start;
}
else
{
lean_dec(v_a_5648_);
return v___x_5687_;
}
}
else
{
lean_object* v_a_5690_; lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5697_; 
lean_dec_ref(v___f_5683_);
lean_dec(v_a_5648_);
v_a_5690_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5697_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5697_ == 0)
{
v___x_5692_ = v___x_5684_;
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
else
{
lean_inc(v_a_5690_);
lean_dec(v___x_5684_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5697_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5695_; 
if (v_isShared_5693_ == 0)
{
v___x_5695_ = v___x_5692_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5696_; 
v_reuseFailAlloc_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5696_, 0, v_a_5690_);
v___x_5695_ = v_reuseFailAlloc_5696_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
return v___x_5695_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5646_ = stack[0].m_obj;
lean_object* v_enterArgsAndSeps_5647_ = stack[1].m_obj;
lean_object* v_a_5648_ = stack[2].m_obj;
lean_object* v_b_5649_ = stack[3].m_obj;
lean_object* v___y_5650_ = stack[4].m_obj;
lean_object* v___y_5651_ = stack[5].m_obj;
lean_object* v___y_5652_ = stack[6].m_obj;
lean_object* v___y_5653_ = stack[7].m_obj;
lean_object* v___y_5654_ = stack[8].m_obj;
lean_object* v___y_5655_ = stack[9].m_obj;
lean_object* v___y_5656_ = stack[10].m_obj;
lean_object* v___y_5657_ = stack[11].m_obj;
lean_object* v_res_5702_;
v_res_5702_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5646_, v_enterArgsAndSeps_5647_, v_a_5648_, v_b_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
stack->m_obj
 = v_res_5702_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___boxed(lean_object* v_upperBound_5703_, lean_object* v_enterArgsAndSeps_5704_, lean_object* v_a_5705_, lean_object* v_b_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v_res_5716_; 
v_res_5716_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5703_, v_enterArgsAndSeps_5704_, v_a_5705_, v_b_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_);
lean_dec(v___y_5714_);
lean_dec_ref(v___y_5713_);
lean_dec(v___y_5712_);
lean_dec_ref(v___y_5711_);
lean_dec(v___y_5710_);
lean_dec_ref(v___y_5709_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
lean_dec_ref(v_enterArgsAndSeps_5704_);
lean_dec(v_upperBound_5703_);
return v_res_5716_;
}
}
lean_object* l_Lean_Elab_Tactic_Conv_evalEnter(lean_object* v_stx_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_){
_start:
{
lean_object* v___x_5729_; lean_object* v_token_5730_; lean_object* v___x_5731_; lean_object* v_lbrak_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v_enterArgsAndSeps_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___f_5743_; lean_object* v___x_5744_; 
v___x_5729_ = lean_unsigned_to_nat(0u);
v_token_5730_ = l_Lean_Syntax_getArg(v_stx_5719_, v___x_5729_);
v___x_5731_ = lean_unsigned_to_nat(1u);
v_lbrak_5732_ = l_Lean_Syntax_getArg(v_stx_5719_, v___x_5731_);
v___x_5733_ = lean_unsigned_to_nat(2u);
v___x_5734_ = l_Lean_Syntax_getArg(v_stx_5719_, v___x_5733_);
v_enterArgsAndSeps_5735_ = l_Lean_Syntax_getArgs(v___x_5734_);
lean_dec(v___x_5734_);
v___x_5736_ = lean_mk_empty_array_with_capacity(v___x_5733_);
v___x_5737_ = lean_array_push(v___x_5736_, v_token_5730_);
v___x_5738_ = lean_array_push(v___x_5737_, v_lbrak_5732_);
v___x_5739_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg___closed__1));
v___x_5740_ = lean_box(2);
v___x_5741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5740_);
lean_ctor_set(v___x_5741_, 1, v___x_5739_);
lean_ctor_set(v___x_5741_, 2, v___x_5738_);
v___x_5742_ = lean_box(0);
v___f_5743_ = ((lean_object*)(l_Lean_Elab_Tactic_Conv_evalEnter___closed__0));
v___x_5744_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(v___x_5741_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5744_) == 0)
{
lean_object* v_a_5745_; lean_object* v___f_5746_; lean_object* v___x_5747_; 
v_a_5745_ = lean_ctor_get(v___x_5744_, 0);
lean_inc(v_a_5745_);
lean_dec_ref_known(v___x_5744_, 1);
v___f_5746_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___lam__1___boxed), 11, 1);
lean_closure_set(v___f_5746_, 0, v_a_5745_);
v___x_5747_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v___f_5743_, v___f_5746_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; 
lean_dec_ref_known(v___x_5747_, 1);
v___x_5748_ = lean_array_get_size(v_enterArgsAndSeps_5735_);
v___x_5749_ = lean_nat_add(v___x_5748_, v___x_5731_);
v___x_5750_ = lean_nat_shiftr(v___x_5749_, v___x_5731_);
lean_dec(v___x_5749_);
v___x_5751_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v___x_5750_, v_enterArgsAndSeps_5735_, v___x_5729_, v___x_5742_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
lean_dec_ref(v_enterArgsAndSeps_5735_);
lean_dec(v___x_5750_);
if (lean_obj_tag(v___x_5751_) == 0)
{
lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5758_; 
v_isSharedCheck_5758_ = !lean_is_exclusive(v___x_5751_);
if (v_isSharedCheck_5758_ == 0)
{
lean_object* v_unused_5759_; 
v_unused_5759_ = lean_ctor_get(v___x_5751_, 0);
lean_dec(v_unused_5759_);
v___x_5753_ = v___x_5751_;
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
else
{
lean_dec(v___x_5751_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5756_; 
if (v_isShared_5754_ == 0)
{
lean_ctor_set(v___x_5753_, 0, v___x_5742_);
v___x_5756_ = v___x_5753_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5742_);
v___x_5756_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
return v___x_5756_;
}
}
}
else
{
return v___x_5751_;
}
}
else
{
lean_dec_ref(v_enterArgsAndSeps_5735_);
return v___x_5747_;
}
}
else
{
lean_object* v_a_5760_; lean_object* v___x_5762_; uint8_t v_isShared_5763_; uint8_t v_isSharedCheck_5767_; 
lean_dec_ref(v_enterArgsAndSeps_5735_);
v_a_5760_ = lean_ctor_get(v___x_5744_, 0);
v_isSharedCheck_5767_ = !lean_is_exclusive(v___x_5744_);
if (v_isSharedCheck_5767_ == 0)
{
v___x_5762_ = v___x_5744_;
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
else
{
lean_inc(v_a_5760_);
lean_dec(v___x_5744_);
v___x_5762_ = lean_box(0);
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
v_resetjp_5761_:
{
lean_object* v___x_5765_; 
if (v_isShared_5763_ == 0)
{
v___x_5765_ = v___x_5762_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_a_5760_);
v___x_5765_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
return v___x_5765_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Conv_evalEnter_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_5719_ = stack[0].m_obj;
lean_object* v_a_5720_ = stack[1].m_obj;
lean_object* v_a_5721_ = stack[2].m_obj;
lean_object* v_a_5722_ = stack[3].m_obj;
lean_object* v_a_5723_ = stack[4].m_obj;
lean_object* v_a_5724_ = stack[5].m_obj;
lean_object* v_a_5725_ = stack[6].m_obj;
lean_object* v_a_5726_ = stack[7].m_obj;
lean_object* v_a_5727_ = stack[8].m_obj;
lean_object* v_res_5768_;
v_res_5768_ = l_Lean_Elab_Tactic_Conv_evalEnter(v_stx_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
stack->m_obj
 = v_res_5768_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Conv_evalEnter___boxed(lean_object* v_stx_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_){
_start:
{
lean_object* v_res_5779_; 
v_res_5779_ = l_Lean_Elab_Tactic_Conv_evalEnter(v_stx_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_);
lean_dec(v_a_5777_);
lean_dec_ref(v_a_5776_);
lean_dec(v_a_5775_);
lean_dec_ref(v_a_5774_);
lean_dec(v_a_5773_);
lean_dec_ref(v_a_5772_);
lean_dec(v_a_5771_);
lean_dec_ref(v_a_5770_);
lean_dec(v_stx_5769_);
return v_res_5779_;
}
}
lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_){
_start:
{
lean_object* v___x_5789_; 
v___x_5789_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___redArg(v___y_5787_);
return v___x_5789_;
}
}
LEAN_EXPORT void l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_5780_ = stack[0].m_obj;
lean_object* v___y_5781_ = stack[1].m_obj;
lean_object* v___y_5782_ = stack[2].m_obj;
lean_object* v___y_5783_ = stack[3].m_obj;
lean_object* v___y_5784_ = stack[4].m_obj;
lean_object* v___y_5785_ = stack[5].m_obj;
lean_object* v___y_5786_ = stack[6].m_obj;
lean_object* v___y_5787_ = stack[7].m_obj;
lean_object* v_res_5790_;
v_res_5790_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
stack->m_obj
 = v_res_5790_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0___boxed(lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_){
_start:
{
lean_object* v_res_5800_; 
v_res_5800_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_spec__0(v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
lean_dec(v___y_5794_);
lean_dec_ref(v___y_5793_);
lean_dec(v___y_5792_);
lean_dec_ref(v___y_5791_);
return v_res_5800_;
}
}
lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_object* v_00_u03b1_5801_, lean_object* v_x_5802_, lean_object* v_mkInfoTree_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_){
_start:
{
lean_object* v___x_5813_; 
v___x_5813_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___redArg(v_x_5802_, v_mkInfoTree_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
return v___x_5813_;
}
}
LEAN_EXPORT void l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5802_ = stack[1].m_obj;
lean_object* v_mkInfoTree_5803_ = stack[2].m_obj;
lean_object* v___y_5804_ = stack[3].m_obj;
lean_object* v___y_5805_ = stack[4].m_obj;
lean_object* v___y_5806_ = stack[5].m_obj;
lean_object* v___y_5807_ = stack[6].m_obj;
lean_object* v___y_5808_ = stack[7].m_obj;
lean_object* v___y_5809_ = stack[8].m_obj;
lean_object* v___y_5810_ = stack[9].m_obj;
lean_object* v___y_5811_ = stack[10].m_obj;
lean_object* v_res_5814_;
v_res_5814_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(lean_box(0), v_x_5802_, v_mkInfoTree_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
stack->m_obj
 = v_res_5814_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0___boxed(lean_object* v_00_u03b1_5815_, lean_object* v_x_5816_, lean_object* v_mkInfoTree_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
lean_object* v_res_5827_; 
v_res_5827_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__0(v_00_u03b1_5815_, v_x_5816_, v_mkInfoTree_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_);
lean_dec(v___y_5825_);
lean_dec_ref(v___y_5824_);
lean_dec(v___y_5823_);
lean_dec_ref(v___y_5822_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
return v_res_5827_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(lean_object* v_upperBound_5828_, lean_object* v_enterArgsAndSeps_5829_, lean_object* v_inst_5830_, lean_object* v_R_5831_, lean_object* v_a_5832_, lean_object* v_b_5833_, lean_object* v_c_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_){
_start:
{
lean_object* v___x_5844_; 
v___x_5844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___redArg(v_upperBound_5828_, v_enterArgsAndSeps_5829_, v_a_5832_, v_b_5833_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_);
return v___x_5844_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5828_ = stack[0].m_obj;
lean_object* v_enterArgsAndSeps_5829_ = stack[1].m_obj;
lean_object* v_a_5832_ = stack[4].m_obj;
lean_object* v_b_5833_ = stack[5].m_obj;
lean_object* v___y_5835_ = stack[7].m_obj;
lean_object* v___y_5836_ = stack[8].m_obj;
lean_object* v___y_5837_ = stack[9].m_obj;
lean_object* v___y_5838_ = stack[10].m_obj;
lean_object* v___y_5839_ = stack[11].m_obj;
lean_object* v___y_5840_ = stack[12].m_obj;
lean_object* v___y_5841_ = stack[13].m_obj;
lean_object* v___y_5842_ = stack[14].m_obj;
lean_object* v_res_5845_;
v_res_5845_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(v_upperBound_5828_, v_enterArgsAndSeps_5829_, lean_box(0), lean_box(0), v_a_5832_, v_b_5833_, lean_box(0), v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_);
stack->m_obj
 = v_res_5845_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1___boxed(lean_object* v_upperBound_5846_, lean_object* v_enterArgsAndSeps_5847_, lean_object* v_inst_5848_, lean_object* v_R_5849_, lean_object* v_a_5850_, lean_object* v_b_5851_, lean_object* v_c_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_){
_start:
{
lean_object* v_res_5862_; 
v_res_5862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Conv_evalEnter_spec__1(v_upperBound_5846_, v_enterArgsAndSeps_5847_, v_inst_5848_, v_R_5849_, v_a_5850_, v_b_5851_, v_c_5852_, v___y_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec(v___y_5858_);
lean_dec_ref(v___y_5857_);
lean_dec(v___y_5856_);
lean_dec_ref(v___y_5855_);
lean_dec(v___y_5854_);
lean_dec_ref(v___y_5853_);
lean_dec_ref(v_enterArgsAndSeps_5847_);
lean_dec(v_upperBound_5846_);
return v_res_5862_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1(){
_start:
{
lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5878_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5879_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__1));
v___x_5880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___closed__3));
v___x_5881_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Conv_evalEnter___boxed), 10, 0);
v___x_5882_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5878_, v___x_5879_, v___x_5880_, v___x_5881_);
return v___x_5882_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5883_;
v_res_5883_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
stack->m_obj
 = v_res_5883_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1___boxed(lean_object* v_a_5884_){
_start:
{
lean_object* v_res_5885_; 
v_res_5885_ = l___private_Lean_Elab_Tactic_Conv_Congr_0__Lean_Elab_Tactic_Conv_evalEnter___regBuiltin_Lean_Elab_Tactic_Conv_evalEnter__1();
return v_res_5885_;
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
