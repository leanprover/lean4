// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.MGoal
// Imports: public import Std.Do.SPred.DerivedLaws public import Std.Tactic.Do.ProofMode public import Lean.Elab.Tactic.Basic
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "uniq"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 18, 161, 16, 33, 3, 130, 7)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 183, 133, 62, 214, 202, 136, 98)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "emptyHyp"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 250, 151, 172, 110, 227, 35, 108)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 97, 27, 109, 96, 85, 230, 202)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "true_and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 45, 192, 15, 224, 238, 244, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "and_true"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(96, 80, 32, 98, 134, 56, 69, 160)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bientails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(201, 51, 221, 5, 242, 131, 169, 118)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(6, 95, 37, 108, 69, 205, 235, 200)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "MGoalEntails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 32, 213, 253, 69, 208, 115, 14)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(203, 9, 83, 52, 40, 85, 31, 178)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 181, 97, 38, 147, 213, 38, 7)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Elab.Tactic.Do.ProofMode.MGoal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "_private.Lean.Elab.Tactic.Do.ProofMode.MGoal.0.Lean.Elab.Tactic.Do.ProofMode.MGoal.findHyp\?.go"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "MGoal.findHyp\?: hypothesis without proper metadata: {e}"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "stray checkHasType "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 96, .m_capacity = 96, .m_length = 95, .m_data = "checkHasType: the expression's inferred type and its expected type did not match.\n\n      expr: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "\n\n      has inferred type: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "\n\n      but the expected type was: "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Ambient state list not a cons "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "mrename_i: Could not find inaccessible hypotheses for "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "MGoalHypMarker"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 32, 213, 253, 69, 208, 115, 14)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 11, 247, 78, 187, 24, 251, 112)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object* v_x_9_){
_start:
{
if (lean_obj_tag(v_x_9_) == 10)
{
lean_object* v_data_10_; 
v_data_10_ = lean_ctor_get(v_x_9_, 0);
lean_inc(v_data_10_);
if (lean_obj_tag(v_data_10_) == 1)
{
lean_object* v_head_11_; lean_object* v_fst_12_; 
v_head_11_ = lean_ctor_get(v_data_10_, 0);
lean_inc(v_head_11_);
v_fst_12_ = lean_ctor_get(v_head_11_, 0);
lean_inc(v_fst_12_);
if (lean_obj_tag(v_fst_12_) == 1)
{
lean_object* v_pre_13_; 
v_pre_13_ = lean_ctor_get(v_fst_12_, 0);
if (lean_obj_tag(v_pre_13_) == 0)
{
lean_object* v_expr_14_; lean_object* v_tail_15_; lean_object* v_snd_16_; lean_object* v_str_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v_expr_14_ = lean_ctor_get(v_x_9_, 1);
lean_inc_ref(v_expr_14_);
lean_dec_ref_known(v_x_9_, 2);
v_tail_15_ = lean_ctor_get(v_data_10_, 1);
lean_inc(v_tail_15_);
lean_dec_ref_known(v_data_10_, 2);
v_snd_16_ = lean_ctor_get(v_head_11_, 1);
lean_inc(v_snd_16_);
lean_dec(v_head_11_);
v_str_17_ = lean_ctor_get(v_fst_12_, 1);
lean_inc_ref(v_str_17_);
lean_dec_ref_known(v_fst_12_, 2);
v___x_18_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0));
v___x_19_ = lean_string_dec_eq(v_str_17_, v___x_18_);
lean_dec_ref(v_str_17_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
lean_dec(v_snd_16_);
lean_dec(v_tail_15_);
lean_dec_ref(v_expr_14_);
v___x_20_ = lean_box(0);
return v___x_20_;
}
else
{
if (lean_obj_tag(v_snd_16_) == 2)
{
if (lean_obj_tag(v_tail_15_) == 1)
{
lean_object* v_head_21_; lean_object* v_fst_22_; 
v_head_21_ = lean_ctor_get(v_tail_15_, 0);
lean_inc(v_head_21_);
v_fst_22_ = lean_ctor_get(v_head_21_, 0);
lean_inc(v_fst_22_);
if (lean_obj_tag(v_fst_22_) == 1)
{
lean_object* v_pre_23_; 
v_pre_23_ = lean_ctor_get(v_fst_22_, 0);
if (lean_obj_tag(v_pre_23_) == 0)
{
lean_object* v_v_24_; lean_object* v_tail_25_; lean_object* v_snd_26_; lean_object* v_str_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v_v_24_ = lean_ctor_get(v_snd_16_, 0);
lean_inc(v_v_24_);
lean_dec_ref_known(v_snd_16_, 1);
v_tail_25_ = lean_ctor_get(v_tail_15_, 1);
lean_inc(v_tail_25_);
lean_dec_ref_known(v_tail_15_, 2);
v_snd_26_ = lean_ctor_get(v_head_21_, 1);
lean_inc(v_snd_26_);
lean_dec(v_head_21_);
v_str_27_ = lean_ctor_get(v_fst_22_, 1);
lean_inc_ref(v_str_27_);
lean_dec_ref_known(v_fst_22_, 2);
v___x_28_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0));
v___x_29_ = lean_string_dec_eq(v_str_27_, v___x_28_);
lean_dec_ref(v_str_27_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; 
lean_dec(v_snd_26_);
lean_dec(v_tail_25_);
lean_dec(v_v_24_);
lean_dec_ref(v_expr_14_);
v___x_30_ = lean_box(0);
return v___x_30_;
}
else
{
if (lean_obj_tag(v_snd_26_) == 2)
{
if (lean_obj_tag(v_tail_25_) == 0)
{
lean_object* v_v_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_v_31_ = lean_ctor_get(v_snd_26_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v_snd_26_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v_snd_26_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_v_31_);
lean_dec(v_snd_26_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_35_, 0, v_v_24_);
lean_ctor_set(v___x_35_, 1, v_v_31_);
lean_ctor_set(v___x_35_, 2, v_expr_14_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v___x_40_; 
lean_dec_ref_known(v_snd_26_, 1);
lean_dec(v_tail_25_);
lean_dec(v_v_24_);
lean_dec_ref(v_expr_14_);
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
else
{
lean_object* v___x_41_; 
lean_dec(v_snd_26_);
lean_dec(v_tail_25_);
lean_dec(v_v_24_);
lean_dec_ref(v_expr_14_);
v___x_41_ = lean_box(0);
return v___x_41_;
}
}
}
else
{
lean_object* v___x_42_; 
lean_dec_ref_known(v_fst_22_, 2);
lean_dec_ref_known(v_tail_15_, 2);
lean_dec(v_head_21_);
lean_dec_ref_known(v_snd_16_, 1);
lean_dec_ref(v_expr_14_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
else
{
lean_object* v___x_43_; 
lean_dec(v_fst_22_);
lean_dec_ref_known(v_tail_15_, 2);
lean_dec(v_head_21_);
lean_dec_ref_known(v_snd_16_, 1);
lean_dec_ref(v_expr_14_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
else
{
lean_object* v___x_44_; 
lean_dec_ref_known(v_snd_16_, 1);
lean_dec(v_tail_15_);
lean_dec_ref(v_expr_14_);
v___x_44_ = lean_box(0);
return v___x_44_;
}
}
else
{
lean_object* v___x_45_; 
lean_dec(v_snd_16_);
lean_dec(v_tail_15_);
lean_dec_ref(v_expr_14_);
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
}
else
{
lean_object* v___x_46_; 
lean_dec_ref_known(v_fst_12_, 2);
lean_dec(v_head_11_);
lean_dec_ref_known(v_data_10_, 2);
lean_dec_ref_known(v_x_9_, 2);
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
else
{
lean_object* v___x_47_; 
lean_dec(v_fst_12_);
lean_dec(v_head_11_);
lean_dec_ref_known(v_data_10_, 2);
lean_dec_ref_known(v_x_9_, 2);
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
else
{
lean_object* v___x_48_; 
lean_dec_ref_known(v_x_9_, 2);
lean_dec(v_data_10_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
else
{
lean_object* v___x_49_; 
lean_dec_ref(v_x_9_);
v___x_49_ = lean_box(0);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object* v_hyp_50_){
_start:
{
lean_object* v_name_51_; lean_object* v_uniq_52_; lean_object* v_p_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_name_51_ = lean_ctor_get(v_hyp_50_, 0);
lean_inc(v_name_51_);
v_uniq_52_ = lean_ctor_get(v_hyp_50_, 1);
lean_inc(v_uniq_52_);
v_p_53_ = lean_ctor_get(v_hyp_50_, 2);
lean_inc_ref(v_p_53_);
lean_dec_ref(v_hyp_50_);
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation));
v___x_55_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_55_, 0, v_name_51_);
v___x_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation));
v___x_58_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_58_, 0, v_uniq_52_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_56_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = l_Lean_Expr_mdata___override(v___x_62_, v_p_53_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType(lean_object* v_u_71_, lean_object* v_00_u03c3s_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3));
v___x_74_ = lean_box(0);
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v_u_71_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = l_Lean_mkConst(v___x_73_, v___x_75_);
v___x_77_ = l_Lean_Expr_app___override(v___x_76_, v_00_u03c3s_72_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object* v_u_84_, lean_object* v_00_u03c3s_85_, lean_object* v_p_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_87_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1));
v___x_88_ = lean_box(0);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v_u_84_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_mkConst(v___x_87_, v___x_89_);
v___x_91_ = l_Lean_mkAppB(v___x_90_, v_00_u03c3s_85_, v_p_86_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_92_) == 5)
{
lean_object* v_fn_93_; 
v_fn_93_ = lean_ctor_get(v_x_92_, 0);
lean_inc_ref(v_fn_93_);
if (lean_obj_tag(v_fn_93_) == 5)
{
lean_object* v_fn_94_; 
v_fn_94_ = lean_ctor_get(v_fn_93_, 0);
lean_inc_ref(v_fn_94_);
if (lean_obj_tag(v_fn_94_) == 4)
{
lean_object* v_declName_95_; 
v_declName_95_ = lean_ctor_get(v_fn_94_, 0);
lean_inc(v_declName_95_);
if (lean_obj_tag(v_declName_95_) == 1)
{
lean_object* v_pre_96_; 
v_pre_96_ = lean_ctor_get(v_declName_95_, 0);
lean_inc(v_pre_96_);
if (lean_obj_tag(v_pre_96_) == 1)
{
lean_object* v_pre_97_; 
v_pre_97_ = lean_ctor_get(v_pre_96_, 0);
lean_inc(v_pre_97_);
if (lean_obj_tag(v_pre_97_) == 1)
{
lean_object* v_pre_98_; 
v_pre_98_ = lean_ctor_get(v_pre_97_, 0);
lean_inc(v_pre_98_);
if (lean_obj_tag(v_pre_98_) == 1)
{
lean_object* v_pre_99_; 
v_pre_99_ = lean_ctor_get(v_pre_98_, 0);
if (lean_obj_tag(v_pre_99_) == 0)
{
lean_object* v_arg_100_; lean_object* v_arg_101_; lean_object* v_us_102_; lean_object* v_str_103_; lean_object* v_str_104_; lean_object* v_str_105_; lean_object* v_str_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_arg_100_ = lean_ctor_get(v_x_92_, 1);
lean_inc_ref(v_arg_100_);
lean_dec_ref_known(v_x_92_, 2);
v_arg_101_ = lean_ctor_get(v_fn_93_, 1);
lean_inc_ref(v_arg_101_);
lean_dec_ref_known(v_fn_93_, 2);
v_us_102_ = lean_ctor_get(v_fn_94_, 1);
lean_inc(v_us_102_);
lean_dec_ref_known(v_fn_94_, 2);
v_str_103_ = lean_ctor_get(v_declName_95_, 1);
lean_inc_ref(v_str_103_);
lean_dec_ref_known(v_declName_95_, 2);
v_str_104_ = lean_ctor_get(v_pre_96_, 1);
lean_inc_ref(v_str_104_);
lean_dec_ref_known(v_pre_96_, 2);
v_str_105_ = lean_ctor_get(v_pre_97_, 1);
lean_inc_ref(v_str_105_);
lean_dec_ref_known(v_pre_97_, 2);
v_str_106_ = lean_ctor_get(v_pre_98_, 1);
lean_inc_ref(v_str_106_);
lean_dec_ref_known(v_pre_98_, 2);
v___x_107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0));
v___x_108_ = lean_string_dec_eq(v_str_106_, v___x_107_);
lean_dec_ref(v_str_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec_ref(v_str_105_);
lean_dec_ref(v_str_104_);
lean_dec_ref(v_str_103_);
lean_dec(v_us_102_);
lean_dec_ref(v_arg_101_);
lean_dec_ref(v_arg_100_);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1));
v___x_111_ = lean_string_dec_eq(v_str_105_, v___x_110_);
lean_dec_ref(v_str_105_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_dec_ref(v_str_104_);
lean_dec_ref(v_str_103_);
lean_dec(v_us_102_);
lean_dec_ref(v_arg_101_);
lean_dec_ref(v_arg_100_);
v___x_112_ = lean_box(0);
return v___x_112_;
}
else
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2));
v___x_114_ = lean_string_dec_eq(v_str_104_, v___x_113_);
lean_dec_ref(v_str_104_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec_ref(v_str_103_);
lean_dec(v_us_102_);
lean_dec_ref(v_arg_101_);
lean_dec_ref(v_arg_100_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0));
v___x_117_ = lean_string_dec_eq(v_str_103_, v___x_116_);
lean_dec_ref(v_str_103_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
lean_dec(v_us_102_);
lean_dec_ref(v_arg_101_);
lean_dec_ref(v_arg_100_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
else
{
if (lean_obj_tag(v_us_102_) == 1)
{
lean_object* v_tail_119_; 
v_tail_119_ = lean_ctor_get(v_us_102_, 1);
if (lean_obj_tag(v_tail_119_) == 0)
{
lean_object* v_head_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_129_; 
v_head_120_ = lean_ctor_get(v_us_102_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v_us_102_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v_us_102_, 1);
lean_dec(v_unused_130_);
v___x_122_ = v_us_102_;
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_head_120_);
lean_dec(v_us_102_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 0);
lean_ctor_set(v___x_122_, 1, v_arg_100_);
lean_ctor_set(v___x_122_, 0, v_arg_101_);
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_arg_101_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_arg_100_);
v___x_125_ = v_reuseFailAlloc_128_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v_head_120_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
}
else
{
lean_object* v___x_131_; 
lean_dec_ref_known(v_us_102_, 2);
lean_dec_ref(v_arg_101_);
lean_dec_ref(v_arg_100_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
else
{
lean_object* v___x_132_; 
lean_dec(v_us_102_);
lean_dec_ref(v_arg_101_);
lean_dec_ref(v_arg_100_);
v___x_132_ = lean_box(0);
return v___x_132_;
}
}
}
}
}
}
else
{
lean_object* v___x_133_; 
lean_dec_ref_known(v_pre_98_, 2);
lean_dec_ref_known(v_pre_97_, 2);
lean_dec_ref_known(v_pre_96_, 2);
lean_dec_ref_known(v_declName_95_, 2);
lean_dec_ref_known(v_fn_94_, 2);
lean_dec_ref_known(v_fn_93_, 2);
lean_dec_ref_known(v_x_92_, 2);
v___x_133_ = lean_box(0);
return v___x_133_;
}
}
else
{
lean_object* v___x_134_; 
lean_dec_ref_known(v_pre_97_, 2);
lean_dec(v_pre_98_);
lean_dec_ref_known(v_pre_96_, 2);
lean_dec_ref_known(v_declName_95_, 2);
lean_dec_ref_known(v_fn_94_, 2);
lean_dec_ref_known(v_fn_93_, 2);
lean_dec_ref_known(v_x_92_, 2);
v___x_134_ = lean_box(0);
return v___x_134_;
}
}
else
{
lean_object* v___x_135_; 
lean_dec(v_pre_97_);
lean_dec_ref_known(v_pre_96_, 2);
lean_dec_ref_known(v_declName_95_, 2);
lean_dec_ref_known(v_fn_94_, 2);
lean_dec_ref_known(v_fn_93_, 2);
lean_dec_ref_known(v_x_92_, 2);
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
else
{
lean_object* v___x_136_; 
lean_dec(v_pre_96_);
lean_dec_ref_known(v_declName_95_, 2);
lean_dec_ref_known(v_fn_94_, 2);
lean_dec_ref_known(v_fn_93_, 2);
lean_dec_ref_known(v_x_92_, 2);
v___x_136_ = lean_box(0);
return v___x_136_;
}
}
else
{
lean_object* v___x_137_; 
lean_dec_ref_known(v_fn_94_, 2);
lean_dec(v_declName_95_);
lean_dec_ref_known(v_fn_93_, 2);
lean_dec_ref_known(v_x_92_, 2);
v___x_137_ = lean_box(0);
return v___x_137_;
}
}
else
{
lean_object* v___x_138_; 
lean_dec_ref_known(v_fn_93_, 2);
lean_dec_ref(v_fn_94_);
lean_dec_ref_known(v_x_92_, 2);
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
else
{
lean_object* v___x_139_; 
lean_dec_ref(v_fn_93_);
lean_dec_ref_known(v_x_92_, 2);
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
else
{
lean_object* v___x_140_; 
lean_dec_ref(v_x_92_);
v___x_140_ = lean_box(0);
return v___x_140_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1));
v___x_150_ = l_Lean_mkConst(v___x_149_, v___x_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(lean_object* v_u_151_, lean_object* v_00_u03c3s_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName));
v___x_154_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2);
v___x_155_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_151_, v_00_u03c3s_152_, v___x_154_);
v___x_156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_156_, 0, v___x_153_);
lean_ctor_set(v___x_156_, 1, v___x_153_);
lean_ctor_set(v___x_156_, 2, v___x_155_);
v___x_157_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(lean_object* v_e_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_158_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v_val_161_; lean_object* v_name_162_; lean_object* v_p_163_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_val_161_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_161_);
lean_dec_ref_known(v___x_159_, 1);
v_name_162_ = lean_ctor_get(v_val_161_, 0);
lean_inc(v_name_162_);
v_p_163_ = lean_ctor_get(v_val_161_, 2);
lean_inc_ref(v_p_163_);
lean_dec(v_val_161_);
v___x_196_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName));
v___x_197_ = lean_name_eq(v_name_162_, v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = l_Lean_Name_hasMacroScopes(v_name_162_);
lean_dec(v_name_162_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_dec_ref(v_p_163_);
v___x_199_ = lean_box(0);
return v___x_199_;
}
else
{
goto v___jp_164_;
}
}
else
{
lean_dec(v_name_162_);
goto v___jp_164_;
}
v___jp_164_:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(v_p_163_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v_val_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_195_; 
v_val_167_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_195_ == 0)
{
v___x_169_ = v___x_165_;
v_isShared_170_ = v_isSharedCheck_195_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_val_167_);
lean_dec(v___x_165_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_195_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v_snd_171_; lean_object* v_snd_172_; 
v_snd_171_ = lean_ctor_get(v_val_167_, 1);
lean_inc(v_snd_171_);
v_snd_172_ = lean_ctor_get(v_snd_171_, 1);
if (lean_obj_tag(v_snd_172_) == 4)
{
lean_object* v_declName_173_; 
v_declName_173_ = lean_ctor_get(v_snd_172_, 0);
lean_inc(v_declName_173_);
if (lean_obj_tag(v_declName_173_) == 1)
{
lean_object* v_pre_174_; 
v_pre_174_ = lean_ctor_get(v_declName_173_, 0);
if (lean_obj_tag(v_pre_174_) == 0)
{
lean_object* v_fst_175_; lean_object* v_fst_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_190_; 
v_fst_175_ = lean_ctor_get(v_val_167_, 0);
lean_inc(v_fst_175_);
lean_dec(v_val_167_);
v_fst_176_ = lean_ctor_get(v_snd_171_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v_snd_171_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v_snd_171_, 1);
lean_dec(v_unused_191_);
v___x_178_ = v_snd_171_;
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_fst_176_);
lean_dec(v_snd_171_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_190_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_str_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v_str_180_ = lean_ctor_get(v_declName_173_, 1);
lean_inc_ref(v_str_180_);
lean_dec_ref_known(v_declName_173_, 2);
v___x_181_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0));
v___x_182_ = lean_string_dec_eq(v_str_180_, v___x_181_);
lean_dec_ref(v_str_180_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; 
lean_del_object(v___x_178_);
lean_dec(v_fst_176_);
lean_dec(v_fst_175_);
lean_del_object(v___x_169_);
v___x_183_ = lean_box(0);
return v___x_183_;
}
else
{
lean_object* v___x_185_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 1, v_fst_176_);
lean_ctor_set(v___x_178_, 0, v_fst_175_);
v___x_185_ = v___x_178_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_fst_175_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_fst_176_);
v___x_185_ = v_reuseFailAlloc_189_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v___x_187_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v___x_185_);
v___x_187_ = v___x_169_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v___x_192_; 
lean_dec_ref_known(v_declName_173_, 2);
lean_dec(v_snd_171_);
lean_del_object(v___x_169_);
lean_dec(v_val_167_);
v___x_192_ = lean_box(0);
return v___x_192_;
}
}
else
{
lean_object* v___x_193_; 
lean_dec(v_declName_173_);
lean_dec(v_snd_171_);
lean_del_object(v___x_169_);
lean_dec(v_val_167_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v_snd_171_);
lean_del_object(v___x_169_);
lean_dec(v_val_167_);
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(lean_object* v_pos_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_unsigned_to_nat(3u);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_201_, v___x_202_, v_pos_200_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct___boxed(lean_object* v_pos_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_pos_204_);
lean_dec(v_pos_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(lean_object* v_pos_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_unsigned_to_nat(3u);
v___x_208_ = lean_unsigned_to_nat(2u);
v___x_209_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_207_, v___x_208_, v_pos_206_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct___boxed(lean_object* v_pos_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_pos_210_);
lean_dec(v_pos_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object* v_u_218_, lean_object* v_00_u03c3s_219_, lean_object* v_lhs_220_, lean_object* v_rhs_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1));
v___x_223_ = lean_box(0);
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v_u_218_);
lean_ctor_set(v___x_224_, 1, v___x_223_);
v___x_225_ = l_Lean_mkConst(v___x_222_, v___x_224_);
v___x_226_ = l_Lean_mkApp3(v___x_225_, v_00_u03c3s_219_, v_lhs_220_, v_rhs_221_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object* v_u_247_, lean_object* v_00_u03c3s_248_, lean_object* v_lhs_249_, lean_object* v_rhs_250_){
_start:
{
lean_object* v___x_251_; 
lean_inc_ref(v_lhs_249_);
v___x_251_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_lhs_249_);
if (lean_obj_tag(v___x_251_) == 1)
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec_ref_known(v___x_251_, 1);
lean_dec_ref(v_lhs_249_);
v___x_252_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1));
v___x_253_ = lean_box(0);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v_u_247_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = l_Lean_mkConst(v___x_252_, v___x_254_);
lean_inc_ref(v_rhs_250_);
v___x_256_ = l_Lean_mkAppB(v___x_255_, v_00_u03c3s_248_, v_rhs_250_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_rhs_250_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
lean_dec(v___x_251_);
lean_inc_ref(v_rhs_250_);
v___x_258_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_rhs_250_);
if (lean_obj_tag(v___x_258_) == 1)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref_known(v___x_258_, 1);
lean_dec_ref(v_rhs_250_);
v___x_259_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3));
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v_u_247_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = l_Lean_mkConst(v___x_259_, v___x_261_);
lean_inc_ref(v_lhs_249_);
v___x_263_ = l_Lean_mkAppB(v___x_262_, v_00_u03c3s_248_, v_lhs_249_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_lhs_249_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
return v___x_264_;
}
else
{
lean_object* v_result_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v___x_258_);
lean_inc_ref(v_00_u03c3s_248_);
lean_inc(v_u_247_);
v_result_265_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_247_, v_00_u03c3s_248_, v_lhs_249_, v_rhs_250_);
v___x_266_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6));
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v_u_247_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_mkConst(v___x_266_, v___x_268_);
lean_inc_ref(v_result_265_);
v___x_270_ = l_Lean_mkAppB(v___x_269_, v_00_u03c3s_248_, v_result_265_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v_result_265_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
return v___x_271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(lean_object* v_u_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_276_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1));
v___x_277_ = l_Lean_Level_succ___override(v_u_275_);
v___x_278_ = lean_box(0);
lean_inc(v___x_277_);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_mkConst(v___x_276_, v___x_279_);
v___x_281_ = l_Lean_mkSort(v___x_277_);
v___x_282_ = l_Lean_Expr_app___override(v___x_280_, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(lean_object* v_u_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_288_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1));
v___x_289_ = l_Lean_Level_succ___override(v_u_287_);
v___x_290_ = lean_box(0);
lean_inc(v___x_289_);
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_mkConst(v___x_288_, v___x_291_);
v___x_293_ = l_Lean_mkSort(v___x_289_);
v___x_294_ = l_Lean_Expr_app___override(v___x_292_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(lean_object* v_u_299_, lean_object* v_hd_300_, lean_object* v_tl_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_302_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1));
v___x_303_ = l_Lean_Level_succ___override(v_u_299_);
v___x_304_ = lean_box(0);
lean_inc(v___x_303_);
v___x_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = l_Lean_mkConst(v___x_302_, v___x_305_);
v___x_307_ = l_Lean_mkSort(v___x_303_);
v___x_308_ = l_Lean_mkApp3(v___x_306_, v___x_307_, v_hd_300_, v_tl_301_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(lean_object* v_a_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_348_; 
v_fst_315_ = lean_ctor_get(v_a_309_, 0);
v_snd_316_ = lean_ctor_get(v_a_309_, 1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_a_309_);
if (v_isSharedCheck_348_ == 0)
{
v___x_318_ = v_a_309_;
v_isShared_319_ = v_isSharedCheck_348_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_snd_316_);
lean_inc(v_fst_315_);
lean_dec(v_a_309_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_348_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1));
v___x_321_ = lean_unsigned_to_nat(3u);
v___x_322_ = l_Lean_Expr_isAppOfArity(v_fst_315_, v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_324_; 
if (v_isShared_319_ == 0)
{
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_315_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_snd_316_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_snd_316_, v___x_327_);
lean_dec(v_snd_316_);
v___x_329_ = lean_unsigned_to_nat(2u);
v___x_330_ = l_Lean_Expr_getAppNumArgs(v_fst_315_);
v___x_331_ = lean_nat_sub(v___x_330_, v___x_329_);
lean_dec(v___x_330_);
v___x_332_ = lean_nat_sub(v___x_331_, v___x_327_);
lean_dec(v___x_331_);
v___x_333_ = l_Lean_Expr_getRevArg_x21(v_fst_315_, v___x_332_);
lean_dec(v_fst_315_);
v___x_334_ = l_Lean_Meta_whnfR(v___x_333_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v___x_328_);
lean_ctor_set(v___x_318_, 0, v_a_335_);
v___x_337_ = v___x_318_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_335_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_328_);
v___x_337_ = v_reuseFailAlloc_339_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
v_a_309_ = v___x_337_;
goto _start;
}
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v___x_328_);
lean_del_object(v___x_318_);
v_a_340_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_334_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_334_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg___boxed(lean_object* v_a_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(lean_object* v_00_u03c3s_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_whnfR(v_00_u03c3s_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_a_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v___x_365_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_375_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v_snd_371_; lean_object* v___x_373_; 
v_snd_371_ = lean_ctor_get(v_a_367_, 1);
lean_inc(v_snd_371_);
lean_dec(v_a_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v_snd_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_snd_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
v_a_376_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_366_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_366_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_a_384_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_362_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_362_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length___boxed(lean_object* v_00_u03c3s_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(v_00_u03c3s_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(lean_object* v_inst_399_, lean_object* v_a_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___boxed(lean_object* v_inst_407_, lean_object* v_a_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(v_inst_407_, v_a_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object* v_e_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1));
v___x_417_ = lean_unsigned_to_nat(3u);
v___x_418_ = l_Lean_Expr_isAppOfArity(v_e_415_, v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_box(0);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_420_ = lean_box(0);
v___x_421_ = l_Lean_Expr_appFn_x21(v_e_415_);
v___x_422_ = l_Lean_Expr_appFn_x21(v___x_421_);
v___x_423_ = l_Lean_Expr_appArg_x21(v___x_422_);
lean_dec_ref(v___x_422_);
v___x_424_ = l_Lean_Expr_appArg_x21(v___x_421_);
lean_dec_ref(v___x_421_);
v___x_425_ = l_Lean_Expr_appArg_x21(v_e_415_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_423_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_Expr_getAppFn(v_e_415_);
v___x_429_ = l_Lean_Expr_constLevels_x21(v___x_428_);
lean_dec_ref(v___x_428_);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = l_List_get_x21Internal___redArg(v___x_420_, v___x_429_, v___x_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_427_);
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f___boxed(lean_object* v_e_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_434_);
lean_dec_ref(v_e_434_);
return v_res_435_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_box(0);
v___x_440_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1));
v___x_441_ = l_Lean_Expr_const___override(v___x_440_, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2);
v___x_443_ = lean_box(0);
v___x_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_442_);
lean_ctor_set(v___x_444_, 3, v___x_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal(void){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default;
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object* v_expr_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_455_ = l_Lean_Expr_consumeMData(v_expr_454_);
v___x_456_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2));
v___x_457_ = lean_unsigned_to_nat(3u);
v___x_458_ = l_Lean_Expr_isAppOfArity(v___x_455_, v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec_ref(v___x_455_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_460_ = lean_box(0);
v___x_461_ = l_Lean_Expr_appFn_x21(v___x_455_);
v___x_462_ = l_Lean_Expr_appFn_x21(v___x_461_);
v___x_463_ = l_Lean_Expr_appArg_x21(v___x_462_);
lean_dec_ref(v___x_462_);
v___x_464_ = l_Lean_Expr_appArg_x21(v___x_461_);
lean_dec_ref(v___x_461_);
v___x_465_ = l_Lean_Expr_appArg_x21(v___x_455_);
lean_dec_ref(v___x_455_);
v___x_466_ = l_Lean_Expr_getAppFn_x27(v_expr_454_);
v___x_467_ = l_Lean_Expr_constLevels_x21(v___x_466_);
lean_dec_ref(v___x_466_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l_List_get_x21Internal___redArg(v___x_460_, v___x_467_, v___x_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_463_);
lean_ctor_set(v___x_470_, 2, v___x_464_);
lean_ctor_set(v___x_470_, 3, v___x_465_);
v___x_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___boxed(lean_object* v_expr_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_expr_472_);
lean_dec_ref(v_expr_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(lean_object* v_e_474_, lean_object* v___y_475_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = l_Lean_Expr_hasMVar(v_e_474_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_e_474_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; lean_object* v_mctx_480_; lean_object* v___x_481_; lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___x_484_; lean_object* v_cache_485_; lean_object* v_zetaDeltaFVarIds_486_; lean_object* v_postponed_487_; lean_object* v_diag_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v___x_479_ = lean_st_ref_get(v___y_475_);
v_mctx_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_mctx_480_);
lean_dec(v___x_479_);
v___x_481_ = l_Lean_instantiateMVarsCore(v_mctx_480_, v_e_474_);
v_fst_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_fst_482_);
v_snd_483_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_snd_483_);
lean_dec_ref(v___x_481_);
v___x_484_ = lean_st_ref_take(v___y_475_);
v_cache_485_ = lean_ctor_get(v___x_484_, 1);
v_zetaDeltaFVarIds_486_ = lean_ctor_get(v___x_484_, 2);
v_postponed_487_ = lean_ctor_get(v___x_484_, 3);
v_diag_488_ = lean_ctor_get(v___x_484_, 4);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_484_, 0);
lean_dec(v_unused_498_);
v___x_490_ = v___x_484_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_diag_488_);
lean_inc(v_postponed_487_);
lean_inc(v_zetaDeltaFVarIds_486_);
lean_inc(v_cache_485_);
lean_dec(v___x_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_snd_483_);
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_snd_483_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_cache_485_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_zetaDeltaFVarIds_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_postponed_487_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_diag_488_);
v___x_493_ = v_reuseFailAlloc_496_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_st_ref_put(v___y_475_, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_fst_482_);
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg___boxed(lean_object* v_e_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_e_499_, v___y_500_);
lean_dec(v___y_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(lean_object* v_e_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_e_503_, v___y_509_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___boxed(lean_object* v_e_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(v_e_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(lean_object* v_msgData_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v___x_531_; lean_object* v_env_532_; uint8_t v___x_533_; lean_object* v_env_534_; lean_object* v___x_535_; lean_object* v_toCold_536_; lean_object* v_mctx_537_; lean_object* v_lctx_538_; lean_object* v_options_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_531_ = lean_st_ref_get(v___y_529_);
v_env_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc_ref(v_env_532_);
lean_dec(v___x_531_);
v___x_533_ = 0;
v_env_534_ = l_Lean_Environment_setRecordingDeps(v_env_532_, v___x_533_);
v___x_535_ = lean_st_ref_get(v___y_527_);
v_toCold_536_ = lean_ctor_get(v___y_528_, 0);
v_mctx_537_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_mctx_537_);
lean_dec(v___x_535_);
v_lctx_538_ = lean_ctor_get(v___y_526_, 2);
v_options_539_ = lean_ctor_get(v_toCold_536_, 2);
lean_inc_ref(v_options_539_);
lean_inc_ref(v_lctx_538_);
v___x_540_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_540_, 0, v_env_534_);
lean_ctor_set(v___x_540_, 1, v_mctx_537_);
lean_ctor_set(v___x_540_, 2, v_lctx_538_);
lean_ctor_set(v___x_540_, 3, v_options_539_);
v___x_541_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v_msgData_525_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1___boxed(lean_object* v_msgData_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msgData_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(lean_object* v_msg_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_ref_556_; lean_object* v___x_557_; lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_566_; 
v_ref_556_ = lean_ctor_get(v___y_553_, 2);
v___x_557_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
v_a_558_ = lean_ctor_get(v___x_557_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_557_);
if (v_isSharedCheck_566_ == 0)
{
v___x_560_ = v___x_557_;
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_557_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_566_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_564_; 
lean_inc(v_ref_556_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v_ref_556_);
lean_ctor_set(v___x_562_, 1, v_a_558_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 1);
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_564_ = v___x_560_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg___boxed(lean_object* v_msg_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v_msg_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_578_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc_n(v_a_587_, 2);
lean_dec_ref_known(v___x_586_, 1);
v___x_588_ = l_Lean_MVarId_getType(v_a_587_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_603_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_a_589_, v_a_582_);
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_603_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_603_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_603_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_591_);
lean_dec(v_a_591_);
if (lean_obj_tag(v___x_595_) == 1)
{
lean_object* v_val_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v_val_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_a_587_);
lean_ctor_set(v___x_597_, 1, v_val_596_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_597_);
v___x_599_ = v___x_593_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v___x_595_);
lean_del_object(v___x_593_);
lean_dec(v_a_587_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1);
v___x_602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v___x_601_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
return v___x_602_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_a_587_);
v_a_604_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_588_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_588_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_586_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_586_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___boxed(lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_);
lean_dec(v_a_627_);
lean_dec_ref(v_a_626_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(lean_object* v_00_u03b1_630_, lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v_msg_631_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___boxed(lean_object* v_00_u03b1_642_, lean_object* v_msg_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(v_00_u03b1_642_, v_msg_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(lean_object* v_goal_660_){
_start:
{
lean_object* v_u_661_; lean_object* v_00_u03c3s_662_; lean_object* v_hyps_663_; lean_object* v_target_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_u_661_ = lean_ctor_get(v_goal_660_, 0);
lean_inc(v_u_661_);
v_00_u03c3s_662_ = lean_ctor_get(v_goal_660_, 1);
lean_inc_ref(v_00_u03c3s_662_);
v_hyps_663_ = lean_ctor_get(v_goal_660_, 2);
lean_inc_ref(v_hyps_663_);
v_target_664_ = lean_ctor_get(v_goal_660_, 3);
lean_inc_ref(v_target_664_);
lean_dec_ref(v_goal_660_);
v___x_665_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1));
v___x_666_ = lean_box(0);
v___x_667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_667_, 0, v_u_661_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_mkConst(v___x_665_, v___x_667_);
v___x_669_ = l_Lean_mkApp3(v___x_668_, v_00_u03c3s_662_, v_hyps_663_, v_target_664_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object* v_goal_670_){
_start:
{
lean_object* v_u_671_; lean_object* v_00_u03c3s_672_; lean_object* v_hyps_673_; lean_object* v_target_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_u_671_ = lean_ctor_get(v_goal_670_, 0);
lean_inc(v_u_671_);
v_00_u03c3s_672_ = lean_ctor_get(v_goal_670_, 1);
lean_inc_ref(v_00_u03c3s_672_);
v_hyps_673_ = lean_ctor_get(v_goal_670_, 2);
lean_inc_ref(v_hyps_673_);
v_target_674_ = lean_ctor_get(v_goal_670_, 3);
lean_inc_ref(v_target_674_);
lean_dec_ref(v_goal_670_);
v___x_675_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2));
v___x_676_ = lean_box(0);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v_u_671_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Lean_mkConst(v___x_675_, v___x_677_);
v___x_679_ = l_Lean_mkApp3(v___x_678_, v_00_u03c3s_672_, v_hyps_673_, v_target_674_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(lean_object* v_msg_680_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_panic_fn_borrowed(v___x_681_, v_msg_680_);
return v___x_682_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2));
v___x_687_ = lean_unsigned_to_nat(8u);
v___x_688_ = lean_unsigned_to_nat(141u);
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1));
v___x_690_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0));
v___x_691_ = l_mkPanicMessageWithDecl(v___x_690_, v___x_689_, v___x_688_, v___x_687_, v___x_686_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(lean_object* v_name_692_, lean_object* v_e_693_, lean_object* v_p_694_){
_start:
{
lean_object* v___x_695_; 
lean_inc_ref(v_e_693_);
v___x_695_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_693_);
if (lean_obj_tag(v___x_695_) == 1)
{
lean_object* v_val_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v_e_693_);
v_val_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_707_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_val_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_name_700_; uint8_t v___x_701_; 
v_name_700_ = lean_ctor_get(v_val_696_, 0);
v___x_701_ = lean_name_eq(v_name_700_, v_name_692_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_del_object(v___x_698_);
lean_dec(v_val_696_);
lean_dec(v_p_694_);
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_p_694_);
lean_ctor_set(v___x_703_, 1, v_val_696_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_703_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_708_; 
lean_dec(v___x_695_);
v___x_708_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_693_);
if (lean_obj_tag(v___x_708_) == 1)
{
lean_object* v_val_709_; lean_object* v_snd_710_; lean_object* v_snd_711_; lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec_ref(v_e_693_);
v_val_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v___x_708_, 1);
v_snd_710_ = lean_ctor_get(v_val_709_, 1);
lean_inc(v_snd_710_);
lean_dec(v_val_709_);
v_snd_711_ = lean_ctor_get(v_snd_710_, 1);
lean_inc(v_snd_711_);
lean_dec(v_snd_710_);
v_fst_712_ = lean_ctor_get(v_snd_711_, 0);
lean_inc(v_fst_712_);
v_snd_713_ = lean_ctor_get(v_snd_711_, 1);
lean_inc(v_snd_713_);
lean_dec(v_snd_711_);
v___x_714_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_p_694_);
v___x_715_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_692_, v_snd_713_, v___x_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_p_694_);
lean_dec(v_p_694_);
v_e_693_ = v_fst_712_;
v_p_694_ = v___x_716_;
goto _start;
}
else
{
lean_dec(v_fst_712_);
lean_dec(v_p_694_);
return v___x_715_;
}
}
else
{
lean_object* v___x_718_; 
lean_dec(v___x_708_);
lean_dec(v_p_694_);
v___x_718_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_693_);
if (lean_obj_tag(v___x_718_) == 1)
{
lean_object* v___x_719_; 
lean_dec_ref_known(v___x_718_, 1);
v___x_719_ = lean_box(0);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v___x_718_);
v___x_720_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3, &l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3);
v___x_721_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(v___x_720_);
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___boxed(lean_object* v_name_722_, lean_object* v_e_723_, lean_object* v_p_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_722_, v_e_723_, v_p_724_);
lean_dec(v_name_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(lean_object* v_goal_726_, lean_object* v_name_727_){
_start:
{
lean_object* v_hyps_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_hyps_728_ = lean_ctor_get(v_goal_726_, 2);
lean_inc_ref(v_hyps_728_);
lean_dec_ref(v_goal_726_);
v___x_729_ = l_Lean_SubExpr_Pos_root;
v___x_730_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_727_, v_hyps_728_, v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f___boxed(lean_object* v_goal_731_, lean_object* v_name_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_731_, v_name_732_);
lean_dec(v_name_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_ref_740_; lean_object* v___x_741_; lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
v_ref_740_ = lean_ctor_get(v___y_737_, 2);
v___x_741_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_750_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
lean_inc(v_ref_740_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_ref_740_);
lean_ctor_set(v___x_746_, 1, v_a_742_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 1);
lean_ctor_set(v___x_744_, 0, v___x_746_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg___boxed(lean_object* v_msg_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v_msg_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_757_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_766_) == 1)
{
lean_object* v_pre_767_; 
v_pre_767_ = lean_ctor_get(v_x_766_, 0);
switch(lean_obj_tag(v_pre_767_))
{
case 1:
{
lean_object* v_pre_768_; 
v_pre_768_ = lean_ctor_get(v_pre_767_, 0);
switch(lean_obj_tag(v_pre_768_))
{
case 0:
{
lean_object* v_str_769_; lean_object* v_str_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_str_769_ = lean_ctor_get(v_x_766_, 1);
v_str_770_ = lean_ctor_get(v_pre_767_, 1);
v___x_771_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_772_ = lean_string_dec_eq(v_str_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0));
v___x_774_ = lean_string_dec_eq(v_str_770_, v___x_773_);
if (v___x_774_ == 0)
{
return v___x_774_;
}
else
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_776_ = lean_string_dec_eq(v_str_769_, v___x_775_);
if (v___x_776_ == 0)
{
return v___x_776_;
}
else
{
return v_suppressElabErrors_765_;
}
}
}
else
{
lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_778_ = lean_string_dec_eq(v_str_769_, v___x_777_);
if (v___x_778_ == 0)
{
return v___x_778_;
}
else
{
return v_suppressElabErrors_765_;
}
}
}
case 1:
{
lean_object* v_pre_779_; 
v_pre_779_ = lean_ctor_get(v_pre_768_, 0);
if (lean_obj_tag(v_pre_779_) == 0)
{
lean_object* v_str_780_; lean_object* v_str_781_; lean_object* v_str_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_str_780_ = lean_ctor_get(v_x_766_, 1);
v_str_781_ = lean_ctor_get(v_pre_767_, 1);
v_str_782_ = lean_ctor_get(v_pre_768_, 1);
v___x_783_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_784_ = lean_string_dec_eq(v_str_782_, v___x_783_);
if (v___x_784_ == 0)
{
return v___x_784_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_786_ = lean_string_dec_eq(v_str_781_, v___x_785_);
if (v___x_786_ == 0)
{
return v___x_786_;
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_788_ = lean_string_dec_eq(v_str_780_, v___x_787_);
if (v___x_788_ == 0)
{
return v___x_788_;
}
else
{
return v_suppressElabErrors_765_;
}
}
}
}
else
{
uint8_t v___x_789_; 
v___x_789_ = 0;
return v___x_789_;
}
}
default: 
{
uint8_t v___x_790_; 
v___x_790_ = 0;
return v___x_790_;
}
}
}
case 0:
{
lean_object* v_str_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_str_791_ = lean_ctor_get(v_x_766_, 1);
v___x_792_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_793_ = lean_string_dec_eq(v_str_791_, v___x_792_);
if (v___x_793_ == 0)
{
return v___x_793_;
}
else
{
return v_suppressElabErrors_765_;
}
}
default: 
{
uint8_t v___x_794_; 
v___x_794_ = 0;
return v___x_794_;
}
}
}
else
{
uint8_t v___x_795_; 
v___x_795_ = 0;
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_suppressElabErrors_boxed_798_; uint8_t v_res_799_; lean_object* v_r_800_; 
v_suppressElabErrors_boxed_798_ = lean_unbox(v_suppressElabErrors_796_);
v_res_799_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_798_, v_x_797_);
lean_dec(v_x_797_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_801_, lean_object* v_opt_802_){
_start:
{
lean_object* v_name_803_; lean_object* v_defValue_804_; lean_object* v_map_805_; lean_object* v___x_806_; 
v_name_803_ = lean_ctor_get(v_opt_802_, 0);
v_defValue_804_ = lean_ctor_get(v_opt_802_, 1);
v_map_805_ = lean_ctor_get(v_opts_801_, 0);
v___x_806_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_805_, v_name_803_);
if (lean_obj_tag(v___x_806_) == 0)
{
uint8_t v___x_807_; 
v___x_807_ = lean_unbox(v_defValue_804_);
return v___x_807_;
}
else
{
lean_object* v_val_808_; 
v_val_808_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_val_808_);
lean_dec_ref_known(v___x_806_, 1);
if (lean_obj_tag(v_val_808_) == 1)
{
uint8_t v_v_809_; 
v_v_809_ = lean_ctor_get_uint8(v_val_808_, 0);
lean_dec_ref_known(v_val_808_, 0);
return v_v_809_;
}
else
{
uint8_t v___x_810_; 
lean_dec(v_val_808_);
v___x_810_ = lean_unbox(v_defValue_804_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_811_, lean_object* v_opt_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_opts_811_, v_opt_812_);
lean_dec_ref(v_opt_812_);
lean_dec_ref(v_opts_811_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(lean_object* v_ref_816_, lean_object* v_msgData_817_, uint8_t v_severity_818_, uint8_t v_isSilent_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; uint8_t v___y_830_; uint8_t v___y_831_; lean_object* v___y_832_; lean_object* v_toCold_833_; lean_object* v___y_834_; lean_object* v___y_863_; lean_object* v___y_864_; uint8_t v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; uint8_t v___y_868_; uint8_t v___y_869_; lean_object* v___y_870_; uint8_t v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; uint8_t v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; uint8_t v___y_900_; uint8_t v___y_901_; uint8_t v___x_911_; uint8_t v___y_913_; uint8_t v___x_919_; 
v___x_911_ = 2;
v___x_919_ = l_Lean_instBEqMessageSeverity_beq(v_severity_818_, v___x_911_);
if (v___x_919_ == 0)
{
v___y_913_ = v___x_919_;
goto v___jp_912_;
}
else
{
uint8_t v___x_920_; 
lean_inc_ref(v_msgData_817_);
v___x_920_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_817_);
if (v___x_920_ == 0)
{
v___y_913_ = v___x_920_;
goto v___jp_912_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_dec_ref(v_msgData_817_);
v___x_921_ = lean_box(0);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
v___jp_825_:
{
lean_object* v_currNamespace_835_; lean_object* v_openDecls_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_env_841_; lean_object* v_nextMacroScope_842_; lean_object* v_ngen_843_; lean_object* v_auxDeclNGen_844_; lean_object* v_traceState_845_; lean_object* v_cache_846_; lean_object* v_recordedDeps_847_; lean_object* v_messages_848_; lean_object* v_infoState_849_; lean_object* v_snapshotTasks_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_861_; 
v_currNamespace_835_ = lean_ctor_get(v_toCold_833_, 4);
v_openDecls_836_ = lean_ctor_get(v_toCold_833_, 5);
lean_inc(v_openDecls_836_);
lean_inc(v_currNamespace_835_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_currNamespace_835_);
lean_ctor_set(v___x_837_, 1, v_openDecls_836_);
v___x_838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___y_827_);
lean_inc_ref(v___y_826_);
lean_inc_ref(v___y_829_);
v___x_839_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_839_, 0, v___y_829_);
lean_ctor_set(v___x_839_, 1, v___y_828_);
lean_ctor_set(v___x_839_, 2, v___y_832_);
lean_ctor_set(v___x_839_, 3, v___y_826_);
lean_ctor_set(v___x_839_, 4, v___x_838_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*5, v___y_831_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*5 + 1, v___y_830_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*5 + 2, v_isSilent_819_);
v___x_840_ = lean_st_ref_take(v___y_834_);
v_env_841_ = lean_ctor_get(v___x_840_, 0);
v_nextMacroScope_842_ = lean_ctor_get(v___x_840_, 1);
v_ngen_843_ = lean_ctor_get(v___x_840_, 2);
v_auxDeclNGen_844_ = lean_ctor_get(v___x_840_, 3);
v_traceState_845_ = lean_ctor_get(v___x_840_, 4);
v_cache_846_ = lean_ctor_get(v___x_840_, 5);
v_recordedDeps_847_ = lean_ctor_get(v___x_840_, 6);
v_messages_848_ = lean_ctor_get(v___x_840_, 7);
v_infoState_849_ = lean_ctor_get(v___x_840_, 8);
v_snapshotTasks_850_ = lean_ctor_get(v___x_840_, 9);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_861_ == 0)
{
v___x_852_ = v___x_840_;
v_isShared_853_ = v_isSharedCheck_861_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snapshotTasks_850_);
lean_inc(v_infoState_849_);
lean_inc(v_messages_848_);
lean_inc(v_recordedDeps_847_);
lean_inc(v_cache_846_);
lean_inc(v_traceState_845_);
lean_inc(v_auxDeclNGen_844_);
lean_inc(v_ngen_843_);
lean_inc(v_nextMacroScope_842_);
lean_inc(v_env_841_);
lean_dec(v___x_840_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_861_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = lean_box(0);
v___x_855_ = l_Lean_MessageLog_add(v___x_839_, v_messages_848_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 7, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_env_841_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_nextMacroScope_842_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_ngen_843_);
lean_ctor_set(v_reuseFailAlloc_860_, 3, v_auxDeclNGen_844_);
lean_ctor_set(v_reuseFailAlloc_860_, 4, v_traceState_845_);
lean_ctor_set(v_reuseFailAlloc_860_, 5, v_cache_846_);
lean_ctor_set(v_reuseFailAlloc_860_, 6, v_recordedDeps_847_);
lean_ctor_set(v_reuseFailAlloc_860_, 7, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_860_, 8, v_infoState_849_);
lean_ctor_set(v_reuseFailAlloc_860_, 9, v_snapshotTasks_850_);
v___x_857_ = v_reuseFailAlloc_860_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_st_ref_put(v___y_834_, v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_854_);
return v___x_859_;
}
}
}
v___jp_862_:
{
lean_object* v_fileName_871_; lean_object* v_fileMap_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_888_; 
v_fileName_871_ = lean_ctor_get(v___y_867_, 0);
v_fileMap_872_ = lean_ctor_get(v___y_867_, 1);
v___x_873_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_817_);
v___x_874_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v___x_873_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_888_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_888_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_888_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_inc_ref_n(v_fileMap_872_, 2);
v___x_879_ = l_Lean_FileMap_toPosition(v_fileMap_872_, v___y_866_);
lean_dec(v___y_866_);
v___x_880_ = l_Lean_FileMap_toPosition(v_fileMap_872_, v___y_870_);
lean_dec(v___y_870_);
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0));
if (v___y_865_ == 0)
{
lean_del_object(v___x_877_);
lean_dec_ref(v___y_864_);
v___y_826_ = v___x_882_;
v___y_827_ = v_a_875_;
v___y_828_ = v___x_879_;
v___y_829_ = v_fileName_871_;
v___y_830_ = v___y_868_;
v___y_831_ = v___y_869_;
v___y_832_ = v___x_881_;
v_toCold_833_ = v___y_863_;
v___y_834_ = v___y_823_;
goto v___jp_825_;
}
else
{
uint8_t v___x_883_; 
lean_inc(v_a_875_);
v___x_883_ = l_Lean_MessageData_hasTag(v___y_864_, v_a_875_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
lean_dec_ref_known(v___x_881_, 1);
lean_dec_ref(v___x_879_);
lean_dec(v_a_875_);
v___x_884_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_884_);
v___x_886_ = v___x_877_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_del_object(v___x_877_);
v___y_826_ = v___x_882_;
v___y_827_ = v_a_875_;
v___y_828_ = v___x_879_;
v___y_829_ = v_fileName_871_;
v___y_830_ = v___y_868_;
v___y_831_ = v___y_869_;
v___y_832_ = v___x_881_;
v_toCold_833_ = v___y_863_;
v___y_834_ = v___y_823_;
goto v___jp_825_;
}
}
}
}
v___jp_889_:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Syntax_getTailPos_x3f(v___y_893_, v___y_895_);
lean_dec(v___y_893_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_inc(v___y_896_);
v___y_863_ = v___y_891_;
v___y_864_ = v___y_892_;
v___y_865_ = v___y_890_;
v___y_866_ = v___y_896_;
v___y_867_ = v___y_891_;
v___y_868_ = v___y_894_;
v___y_869_ = v___y_895_;
v___y_870_ = v___y_896_;
goto v___jp_862_;
}
else
{
lean_object* v_val_898_; 
v_val_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v___x_897_, 1);
v___y_863_ = v___y_891_;
v___y_864_ = v___y_892_;
v___y_865_ = v___y_890_;
v___y_866_ = v___y_896_;
v___y_867_ = v___y_891_;
v___y_868_ = v___y_894_;
v___y_869_ = v___y_895_;
v___y_870_ = v_val_898_;
goto v___jp_862_;
}
}
v___jp_899_:
{
lean_object* v_toCold_902_; lean_object* v_ref_903_; uint8_t v_suppressElabErrors_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v_ref_907_; lean_object* v___x_908_; 
v_toCold_902_ = lean_ctor_get(v___y_822_, 0);
v_ref_903_ = lean_ctor_get(v___y_822_, 2);
v_suppressElabErrors_904_ = lean_ctor_get_uint8(v___y_822_, sizeof(void*)*3 + 2);
v___x_905_ = lean_box(v_suppressElabErrors_904_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_906_, 0, v___x_905_);
v_ref_907_ = l_Lean_replaceRef(v_ref_816_, v_ref_903_);
v___x_908_ = l_Lean_Syntax_getPos_x3f(v_ref_907_, v___y_900_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___y_890_ = v_suppressElabErrors_904_;
v___y_891_ = v_toCold_902_;
v___y_892_ = v___f_906_;
v___y_893_ = v_ref_907_;
v___y_894_ = v___y_901_;
v___y_895_ = v___y_900_;
v___y_896_ = v___x_909_;
goto v___jp_889_;
}
else
{
lean_object* v_val_910_; 
v_val_910_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_val_910_);
lean_dec_ref_known(v___x_908_, 1);
v___y_890_ = v_suppressElabErrors_904_;
v___y_891_ = v_toCold_902_;
v___y_892_ = v___f_906_;
v___y_893_ = v_ref_907_;
v___y_894_ = v___y_901_;
v___y_895_ = v___y_900_;
v___y_896_ = v_val_910_;
goto v___jp_889_;
}
}
v___jp_912_:
{
uint8_t v___x_914_; uint8_t v___x_915_; 
v___x_914_ = 1;
v___x_915_ = l_Lean_instBEqMessageSeverity_beq(v_severity_818_, v___x_914_);
if (v___x_915_ == 0)
{
v___y_900_ = v___y_913_;
v___y_901_ = v_severity_818_;
goto v___jp_899_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_822_);
v___x_917_ = l_Lean_warningAsError;
v___x_918_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v___x_916_, v___x_917_);
lean_dec_ref(v___x_916_);
if (v___x_918_ == 0)
{
v___y_900_ = v___y_913_;
v___y_901_ = v_severity_818_;
goto v___jp_899_;
}
else
{
v___y_900_ = v___y_913_;
v___y_901_ = v___x_911_;
goto v___jp_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_923_, lean_object* v_msgData_924_, lean_object* v_severity_925_, lean_object* v_isSilent_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
uint8_t v_severity_boxed_932_; uint8_t v_isSilent_boxed_933_; lean_object* v_res_934_; 
v_severity_boxed_932_ = lean_unbox(v_severity_925_);
v_isSilent_boxed_933_ = lean_unbox(v_isSilent_926_);
v_res_934_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_923_, v_msgData_924_, v_severity_boxed_932_, v_isSilent_boxed_933_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_ref_923_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(lean_object* v_msgData_935_, uint8_t v_severity_936_, uint8_t v_isSilent_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_ref_943_; lean_object* v___x_944_; 
v_ref_943_ = lean_ctor_get(v___y_940_, 2);
v___x_944_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_943_, v_msgData_935_, v_severity_936_, v_isSilent_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0___boxed(lean_object* v_msgData_945_, lean_object* v_severity_946_, lean_object* v_isSilent_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
uint8_t v_severity_boxed_953_; uint8_t v_isSilent_boxed_954_; lean_object* v_res_955_; 
v_severity_boxed_953_ = lean_unbox(v_severity_946_);
v_isSilent_boxed_954_ = lean_unbox(v_isSilent_947_);
v_res_955_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_945_, v_severity_boxed_953_, v_isSilent_boxed_954_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(lean_object* v_msgData_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; 
v___x_962_ = 1;
v___x_963_ = 0;
v___x_964_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_956_, v___x_962_, v___x_963_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0___boxed(lean_object* v_msgData_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v_msgData_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_971_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(lean_object* v_expr_987_, lean_object* v_expectedType_988_, uint8_t v_suppressWarning_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_){
_start:
{
lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; uint8_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = 0;
lean_inc_ref(v_expr_987_);
v___x_1011_ = l_Lean_Meta_check(v_expr_987_, v___x_1010_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1012_; 
lean_dec_ref_known(v___x_1011_, 1);
lean_inc_ref(v_expectedType_988_);
v___x_1012_ = l_Lean_Meta_check(v_expectedType_988_, v___x_1010_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v___x_1013_; 
lean_dec_ref_known(v___x_1012_, 1);
lean_inc(v_a_993_);
lean_inc_ref(v_a_992_);
lean_inc(v_a_991_);
lean_inc_ref(v_a_990_);
lean_inc_ref(v_expr_987_);
v___x_1013_ = lean_infer_type(v_expr_987_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_n(v_a_1014_, 2);
lean_dec_ref_known(v___x_1013_, 1);
lean_inc_ref(v_expectedType_988_);
v___x_1015_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1014_, v_expectedType_988_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; uint8_t v___x_1017_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_unbox(v_a_1016_);
lean_dec(v_a_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1018_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5);
v___x_1019_ = l_Lean_indentExpr(v_expr_987_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_indentExpr(v_a_1014_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_indentExpr(v_expectedType_988_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1028_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
return v___x_1029_;
}
else
{
lean_dec(v_a_1014_);
v___y_996_ = v_a_990_;
v___y_997_ = v_a_991_;
v___y_998_ = v_a_992_;
v___y_999_ = v_a_993_;
goto v___jp_995_;
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_a_1014_);
lean_dec_ref(v_expectedType_988_);
lean_dec_ref(v_expr_987_);
v_a_1030_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1015_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1015_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_expectedType_988_);
lean_dec_ref(v_expr_987_);
v_a_1038_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1013_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1013_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_988_);
lean_dec_ref(v_expr_987_);
return v___x_1012_;
}
}
else
{
lean_dec_ref(v_expectedType_988_);
lean_dec_ref(v_expr_987_);
return v___x_1011_;
}
v___jp_995_:
{
if (v_suppressWarning_989_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1000_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1);
v___x_1001_ = l_Lean_MessageData_ofExpr(v_expr_987_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_MessageData_ofExpr(v_expectedType_988_);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v___x_1006_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref(v_expectedType_988_);
lean_dec_ref(v_expr_987_);
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___boxed(lean_object* v_expr_1046_, lean_object* v_expectedType_1047_, lean_object* v_suppressWarning_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
uint8_t v_suppressWarning_boxed_1054_; lean_object* v_res_1055_; 
v_suppressWarning_boxed_1054_ = lean_unbox(v_suppressWarning_1048_);
v_res_1055_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(v_expr_1046_, v_expectedType_1047_, v_suppressWarning_boxed_1054_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(lean_object* v_00_u03b1_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v_msg_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(v_00_u03b1_1064_, v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(lean_object* v_goal_1072_, lean_object* v_prf_1073_, uint8_t v_suppressWarning_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1072_);
v___x_1081_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(v_prf_1073_, v___x_1080_, v_suppressWarning_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof___boxed(lean_object* v_goal_1082_, lean_object* v_prf_1083_, lean_object* v_suppressWarning_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
uint8_t v_suppressWarning_boxed_1090_; lean_object* v_res_1091_; 
v_suppressWarning_boxed_1090_ = lean_unbox(v_suppressWarning_1084_);
v_res_1091_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(v_goal_1082_, v_prf_1083_, v_suppressWarning_boxed_1090_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object* v_x_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2));
lean_inc(v_x_1103_);
v___x_1108_ = l_Lean_Syntax_isOfKind(v_x_1103_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4));
v___x_1110_ = l_Lean_Core_mkFreshUserName(v___x_1109_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1119_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_a_1111_);
lean_ctor_set(v___x_1115_, 1, v_x_1103_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_x_1103_);
v_a_1120_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1110_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1110_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v___x_1128_; lean_object* v_name_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v_name_1129_ = l_Lean_Syntax_getArg(v_x_1103_, v___x_1128_);
v___x_1130_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6));
lean_inc(v_name_1129_);
v___x_1131_ = l_Lean_Syntax_isOfKind(v_name_1129_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec(v_name_1129_);
v___x_1132_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4));
v___x_1133_ = l_Lean_Core_mkFreshUserName(v___x_1132_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_a_1134_);
lean_ctor_set(v___x_1138_, 1, v_x_1103_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_x_1103_);
v_a_1143_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1133_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1133_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec(v_x_1103_);
v___x_1151_ = l_Lean_TSyntax_getId(v_name_1129_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
lean_ctor_set(v___x_1152_, 1, v_name_1129_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___boxed(lean_object* v_x_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_x_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(lean_object* v_as_1159_, size_t v_i_1160_, size_t v_stop_1161_, lean_object* v_b_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_usize_dec_eq(v_i_1160_, v_stop_1161_);
if (v___x_1163_ == 0)
{
size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; lean_object* v_snd_1167_; lean_object* v_fst_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; 
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_sub(v_i_1160_, v___x_1164_);
v___x_1166_ = lean_array_uget_borrowed(v_as_1159_, v___x_1165_);
v_snd_1167_ = lean_ctor_get(v___x_1166_, 1);
v_fst_1168_ = lean_ctor_get(v___x_1166_, 0);
v_fst_1169_ = lean_ctor_get(v_snd_1167_, 0);
v_snd_1170_ = lean_ctor_get(v_snd_1167_, 1);
v___x_1171_ = lean_unbox(v_snd_1170_);
lean_inc(v_fst_1169_);
lean_inc(v_fst_1168_);
v___x_1172_ = l_Lean_Expr_lam___override(v_fst_1168_, v_fst_1169_, v_b_1162_, v___x_1171_);
v_i_1160_ = v___x_1165_;
v_b_1162_ = v___x_1172_;
goto _start;
}
else
{
return v_b_1162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0___boxed(lean_object* v_as_1174_, lean_object* v_i_1175_, lean_object* v_stop_1176_, lean_object* v_b_1177_){
_start:
{
size_t v_i_boxed_1178_; size_t v_stop_boxed_1179_; lean_object* v_res_1180_; 
v_i_boxed_1178_ = lean_unbox_usize(v_i_1175_);
lean_dec(v_i_1175_);
v_stop_boxed_1179_ = lean_unbox_usize(v_stop_1176_);
lean_dec(v_stop_1176_);
v_res_1180_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_as_1174_, v_i_boxed_1178_, v_stop_boxed_1179_, v_b_1177_);
lean_dec_ref(v_as_1174_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(lean_object* v_revLams_1181_, lean_object* v_revAppArgs_1182_, lean_object* v_body_1183_){
_start:
{
uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1184_ = 0;
v___x_1185_ = l_Lean_Expr_betaRev(v_body_1183_, v_revAppArgs_1182_, v___x_1184_, v___x_1184_);
v___x_1186_ = lean_array_get_size(v_revLams_1181_);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_nat_dec_lt(v___x_1187_, v___x_1186_);
if (v___x_1188_ == 0)
{
return v___x_1185_;
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_usize_of_nat(v___x_1186_);
v___x_1190_ = ((size_t)0ULL);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_revLams_1181_, v___x_1189_, v___x_1190_, v___x_1185_);
return v___x_1191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap___boxed(lean_object* v_revLams_1192_, lean_object* v_revAppArgs_1193_, lean_object* v_body_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1192_, v_revAppArgs_1193_, v_body_1194_);
lean_dec_ref(v_revAppArgs_1193_);
lean_dec_ref(v_revLams_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(lean_object* v_00_u03c3s_1196_, lean_object* v_revLams_1197_, lean_object* v_revAppArgs_1198_, lean_object* v_e_1199_){
_start:
{
lean_object* v___x_1200_; 
lean_inc_ref(v_e_1199_);
v___x_1200_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_1199_);
if (lean_obj_tag(v___x_1200_) == 1)
{
lean_object* v_val_1201_; lean_object* v_fst_1202_; lean_object* v___x_1203_; 
lean_dec_ref(v_e_1199_);
lean_dec_ref(v_revAppArgs_1198_);
lean_dec_ref(v_revLams_1197_);
v_val_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_val_1201_);
lean_dec_ref_known(v___x_1200_, 1);
v_fst_1202_ = lean_ctor_get(v_val_1201_, 0);
lean_inc(v_fst_1202_);
lean_dec(v_val_1201_);
v___x_1203_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_fst_1202_, v_00_u03c3s_1196_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; 
lean_dec(v___x_1200_);
lean_inc_ref(v_e_1199_);
v___x_1204_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_1199_);
if (lean_obj_tag(v___x_1204_) == 1)
{
lean_object* v_val_1205_; lean_object* v_name_1206_; lean_object* v_uniq_1207_; lean_object* v_p_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_e_1199_);
lean_dec_ref(v_00_u03c3s_1196_);
v_val_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_val_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v_name_1206_ = lean_ctor_get(v_val_1205_, 0);
v_uniq_1207_ = lean_ctor_get(v_val_1205_, 1);
v_p_1208_ = lean_ctor_get(v_val_1205_, 2);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_val_1205_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1210_ = v_val_1205_;
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_p_1208_);
lean_inc(v_uniq_1207_);
lean_inc(v_name_1206_);
lean_dec(v_val_1205_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1217_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1197_, v_revAppArgs_1198_, v_p_1208_);
lean_dec_ref(v_revAppArgs_1198_);
lean_dec_ref(v_revLams_1197_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 2, v___x_1212_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_name_1206_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_uniq_1207_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1214_);
return v___x_1215_;
}
}
}
else
{
lean_object* v___x_1218_; 
lean_dec(v___x_1204_);
v___x_1218_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_1199_);
if (lean_obj_tag(v___x_1218_) == 1)
{
lean_object* v_val_1219_; lean_object* v_snd_1220_; lean_object* v_snd_1221_; lean_object* v_fst_1222_; lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref(v_e_1199_);
v_val_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_val_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v_snd_1220_ = lean_ctor_get(v_val_1219_, 1);
v_snd_1221_ = lean_ctor_get(v_snd_1220_, 1);
lean_inc(v_snd_1221_);
v_fst_1222_ = lean_ctor_get(v_val_1219_, 0);
lean_inc(v_fst_1222_);
lean_dec(v_val_1219_);
v_fst_1223_ = lean_ctor_get(v_snd_1221_, 0);
lean_inc(v_fst_1223_);
v_snd_1224_ = lean_ctor_get(v_snd_1221_, 1);
lean_inc(v_snd_1224_);
lean_dec(v_snd_1221_);
lean_inc_ref(v_revAppArgs_1198_);
lean_inc_ref(v_revLams_1197_);
lean_inc_ref_n(v_00_u03c3s_1196_, 2);
v___x_1225_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1196_, v_revLams_1197_, v_revAppArgs_1198_, v_fst_1223_);
v___x_1226_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1196_, v_revLams_1197_, v_revAppArgs_1198_, v_snd_1224_);
v___x_1227_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_1222_, v_00_u03c3s_1196_, v___x_1225_, v___x_1226_);
return v___x_1227_;
}
else
{
lean_dec(v___x_1218_);
if (lean_obj_tag(v_e_1199_) == 6)
{
lean_object* v_binderName_1228_; lean_object* v_binderType_1229_; lean_object* v_body_1230_; uint8_t v_binderInfo_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_binderName_1228_ = lean_ctor_get(v_e_1199_, 0);
lean_inc(v_binderName_1228_);
v_binderType_1229_ = lean_ctor_get(v_e_1199_, 1);
lean_inc_ref(v_binderType_1229_);
v_body_1230_ = lean_ctor_get(v_e_1199_, 2);
lean_inc_ref(v_body_1230_);
v_binderInfo_1231_ = lean_ctor_get_uint8(v_e_1199_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1199_, 3);
v___x_1232_ = lean_array_get_size(v_revAppArgs_1198_);
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_sub(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_nat_dec_lt(v___x_1234_, v___x_1232_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v___x_1234_);
v___x_1236_ = lean_box(v_binderInfo_1231_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_binderType_1229_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_binderName_1228_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = lean_array_push(v_revLams_1197_, v___x_1238_);
v_revLams_1197_ = v___x_1239_;
v_e_1199_ = v_body_1230_;
goto _start;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v_binderType_1229_);
lean_dec(v_binderName_1228_);
v___x_1241_ = lean_array_fget(v_revAppArgs_1198_, v___x_1234_);
lean_dec(v___x_1234_);
v___x_1242_ = lean_array_pop(v_revAppArgs_1198_);
v___x_1243_ = lean_expr_instantiate1(v_body_1230_, v___x_1241_);
lean_dec(v___x_1241_);
lean_dec_ref(v_body_1230_);
v_revAppArgs_1198_ = v___x_1242_;
v_e_1199_ = v___x_1243_;
goto _start;
}
}
else
{
if (lean_obj_tag(v_e_1199_) == 5)
{
lean_object* v_fn_1245_; lean_object* v_arg_1246_; lean_object* v___x_1247_; 
v_fn_1245_ = lean_ctor_get(v_e_1199_, 0);
lean_inc_ref(v_fn_1245_);
v_arg_1246_ = lean_ctor_get(v_e_1199_, 1);
lean_inc_ref(v_arg_1246_);
lean_dec_ref_known(v_e_1199_, 2);
v___x_1247_ = lean_array_push(v_revAppArgs_1198_, v_arg_1246_);
v_revAppArgs_1198_ = v___x_1247_;
v_e_1199_ = v_fn_1245_;
goto _start;
}
else
{
lean_object* v___x_1249_; 
lean_dec_ref(v_00_u03c3s_1196_);
v___x_1249_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1197_, v_revAppArgs_1198_, v_e_1199_);
lean_dec_ref(v_revAppArgs_1198_);
lean_dec_ref(v_revLams_1197_);
return v___x_1249_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(lean_object* v_00_u03c3s_1252_, lean_object* v_hyps_1253_){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0));
v___x_1255_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1252_, v___x_1254_, v___x_1254_, v_hyps_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(lean_object* v_00_u03c3s_x27_1256_, lean_object* v_e_1257_, lean_object* v_args_1258_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = l_Lean_mkAppN(v_e_1257_, v_args_1258_);
v___x_1260_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v_00_u03c3s_x27_1256_, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames___boxed(lean_object* v_00_u03c3s_x27_1261_, lean_object* v_e_1262_, lean_object* v_args_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(v_00_u03c3s_x27_1261_, v_e_1262_, v_args_1263_);
lean_dec_ref(v_args_1263_);
return v_res_1264_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(lean_object* v_upperBound_1268_, lean_object* v_a_1269_, lean_object* v_b_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_a_1277_; uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_lt(v_a_1269_, v_upperBound_1268_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_a_1269_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_b_1270_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; 
lean_inc_ref(v_b_1270_);
v___x_1283_ = l_Lean_Meta_whnfR(v_b_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1));
v___x_1286_ = lean_unsigned_to_nat(3u);
v___x_1287_ = l_Lean_Expr_isAppOfArity(v_a_1284_, v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v_a_1284_);
v___x_1288_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1);
lean_inc_ref(v_b_1270_);
v___x_1289_ = l_Lean_MessageData_ofExpr(v_b_1270_);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1290_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_dec_ref_known(v___x_1291_, 1);
v_a_1277_ = v_b_1270_;
goto v___jp_1276_;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_b_1270_);
lean_dec(v_a_1269_);
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
else
{
lean_object* v___x_1300_; 
lean_dec_ref(v_b_1270_);
v___x_1300_ = l_Lean_Expr_appArg_x21(v_a_1284_);
lean_dec(v_a_1284_);
v_a_1277_ = v___x_1300_;
goto v___jp_1276_;
}
}
else
{
lean_dec_ref(v_b_1270_);
lean_dec(v_a_1269_);
return v___x_1283_;
}
}
v___jp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_add(v_a_1269_, v___x_1278_);
lean_dec(v_a_1269_);
v_a_1269_ = v___x_1279_;
v_b_1270_ = v_a_1277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___boxed(lean_object* v_upperBound_1301_, lean_object* v_a_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_1301_, v_a_1302_, v_b_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v_upperBound_1301_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(lean_object* v_00_u03c3s_1310_, lean_object* v_n_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_n_1311_, v___x_1317_, v_00_u03c3s_1310_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList___boxed(lean_object* v_00_u03c3s_1319_, lean_object* v_n_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(v_00_u03c3s_1319_, v_n_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_n_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(lean_object* v_upperBound_1327_, lean_object* v_inst_1328_, lean_object* v_R_1329_, lean_object* v_a_1330_, lean_object* v_b_1331_, lean_object* v_c_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_1327_, v_a_1330_, v_b_1331_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___boxed(lean_object* v_upperBound_1339_, lean_object* v_inst_1340_, lean_object* v_R_1341_, lean_object* v_a_1342_, lean_object* v_b_1343_, lean_object* v_c_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(v_upperBound_1339_, v_inst_1340_, v_R_1341_, v_a_1342_, v_b_1343_, v_c_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v_upperBound_1339_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(lean_object* v_H_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
v_fst_1354_ = lean_ctor_get(v_a_1352_, 0);
v_snd_1355_ = lean_ctor_get(v_a_1352_, 1);
v___x_1356_ = lean_array_get_size(v_snd_1355_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_nat_dec_eq(v___x_1356_, v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; 
lean_inc_ref(v_H_1351_);
v___x_1359_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_H_1351_);
if (lean_obj_tag(v___x_1359_) == 1)
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1359_, 0);
lean_dec(v_unused_1368_);
v___x_1361_ = v___x_1359_;
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v___x_1359_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1367_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_H_1351_);
lean_ctor_set(v___x_1363_, 1, v_a_1352_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1363_);
v___x_1365_ = v___x_1361_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
lean_object* v___x_1369_; 
lean_dec(v___x_1359_);
lean_inc_ref(v_H_1351_);
v___x_1369_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_H_1351_);
if (lean_obj_tag(v___x_1369_) == 1)
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1418_; 
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_a_1352_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; lean_object* v_unused_1420_; 
v_unused_1419_ = lean_ctor_get(v_a_1352_, 1);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_a_1352_, 0);
lean_dec(v_unused_1420_);
v___x_1371_ = v_a_1352_;
v_isShared_1372_ = v_isSharedCheck_1418_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_a_1352_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1418_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_val_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1417_; 
v_val_1373_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1375_ = v___x_1369_;
v_isShared_1376_ = v_isSharedCheck_1417_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_val_1373_);
lean_dec(v___x_1369_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1417_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_name_1377_; lean_object* v_uniq_1378_; lean_object* v_p_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1416_; 
v_name_1377_ = lean_ctor_get(v_val_1373_, 0);
v_uniq_1378_ = lean_ctor_get(v_val_1373_, 1);
v_p_1379_ = lean_ctor_get(v_val_1373_, 2);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_val_1373_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1381_ = v_val_1373_;
v_isShared_1382_ = v_isSharedCheck_1416_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_p_1379_);
lean_inc(v_uniq_1378_);
lean_inc(v_name_1377_);
lean_dec(v_val_1373_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1416_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_idents_1384_; uint8_t v___x_1414_; 
v___x_1414_ = l_Lean_Name_hasMacroScopes(v_name_1377_);
if (v___x_1414_ == 0)
{
uint8_t v___x_1415_; 
v___x_1415_ = l_Lean_NameSet_contains(v_fst_1354_, v_name_1377_);
if (v___x_1415_ == 0)
{
lean_del_object(v___x_1381_);
lean_dec_ref(v_p_1379_);
lean_dec(v_uniq_1378_);
v_idents_1384_ = v_snd_1355_;
goto v___jp_1383_;
}
else
{
goto v___jp_1393_;
}
}
else
{
goto v___jp_1393_;
}
v___jp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = l_Lean_NameSet_insert(v_fst_1354_, v_name_1377_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_idents_1384_);
lean_ctor_set(v___x_1371_, 0, v___x_1385_);
v___x_1387_ = v___x_1371_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_idents_1384_);
v___x_1387_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_H_1351_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set_tag(v___x_1375_, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1388_);
v___x_1390_ = v___x_1375_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
v___jp_1393_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1394_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2));
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_sub(v___x_1356_, v___x_1396_);
v___x_1398_ = lean_array_get_borrowed(v___x_1395_, v_snd_1355_, v___x_1397_);
lean_dec(v___x_1397_);
lean_inc(v___x_1398_);
v___x_1399_ = l_Lean_Syntax_isOfKind(v___x_1398_, v___x_1394_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_del_object(v___x_1381_);
lean_dec_ref(v_p_1379_);
lean_dec(v_uniq_1378_);
v___x_1400_ = lean_array_pop(v_snd_1355_);
v_idents_1384_ = v___x_1400_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1401_ = l_Lean_Syntax_getArg(v___x_1398_, v___x_1357_);
v___x_1402_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6));
lean_inc(v___x_1401_);
v___x_1403_ = l_Lean_Syntax_isOfKind(v___x_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; 
lean_dec(v___x_1401_);
lean_del_object(v___x_1381_);
lean_dec_ref(v_p_1379_);
lean_dec(v_uniq_1378_);
v___x_1404_ = lean_array_pop(v_snd_1355_);
v_idents_1384_ = v___x_1404_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_dec(v_name_1377_);
lean_del_object(v___x_1375_);
lean_del_object(v___x_1371_);
lean_dec_ref(v_H_1351_);
v___x_1405_ = l_Lean_TSyntax_getId(v___x_1401_);
lean_dec(v___x_1401_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1405_);
v___x_1407_ = v___x_1381_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_uniq_1378_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_p_1379_);
v___x_1407_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1408_ = lean_array_pop(v_snd_1355_);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_fst_1354_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1407_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1409_);
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
return v___x_1412_;
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
lean_object* v___x_1421_; 
lean_dec(v___x_1369_);
v___x_1421_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_H_1351_);
if (lean_obj_tag(v___x_1421_) == 1)
{
lean_object* v_val_1422_; lean_object* v_snd_1423_; lean_object* v_snd_1424_; lean_object* v_fst_1425_; lean_object* v_fst_1426_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v_H_1351_);
v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v_snd_1423_ = lean_ctor_get(v_val_1422_, 1);
lean_inc(v_snd_1423_);
v_snd_1424_ = lean_ctor_get(v_snd_1423_, 1);
lean_inc(v_snd_1424_);
v_fst_1425_ = lean_ctor_get(v_val_1422_, 0);
lean_inc(v_fst_1425_);
lean_dec(v_val_1422_);
v_fst_1426_ = lean_ctor_get(v_snd_1423_, 0);
lean_inc(v_fst_1426_);
lean_dec(v_snd_1423_);
v_fst_1427_ = lean_ctor_get(v_snd_1424_, 0);
lean_inc(v_fst_1427_);
v_snd_1428_ = lean_ctor_get(v_snd_1424_, 1);
lean_inc(v_snd_1428_);
lean_dec(v_snd_1424_);
v___x_1429_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_snd_1428_, v_a_1352_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1433_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v_fst_1431_ = lean_ctor_get(v_a_1430_, 0);
lean_inc(v_fst_1431_);
v_snd_1432_ = lean_ctor_get(v_a_1430_, 1);
lean_inc(v_snd_1432_);
lean_dec(v_a_1430_);
v___x_1433_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_fst_1427_, v_snd_1432_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1451_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1451_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1451_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_fst_1438_; lean_object* v_snd_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1450_; 
v_fst_1438_ = lean_ctor_get(v_a_1434_, 0);
v_snd_1439_ = lean_ctor_get(v_a_1434_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_a_1434_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1441_ = v_a_1434_;
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_snd_1439_);
lean_inc(v_fst_1438_);
lean_dec(v_a_1434_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1450_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1443_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_1425_, v_fst_1426_, v_fst_1438_, v_fst_1431_);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1439_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1445_);
v___x_1447_ = v___x_1436_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
else
{
lean_dec(v_fst_1431_);
lean_dec(v_fst_1426_);
lean_dec(v_fst_1425_);
return v___x_1433_;
}
}
else
{
lean_dec(v_fst_1427_);
lean_dec(v_fst_1426_);
lean_dec(v_fst_1425_);
return v___x_1429_;
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec(v___x_1421_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_H_1351_);
lean_ctor_set(v___x_1452_, 1, v_a_1352_);
v___x_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
return v___x_1453_;
}
}
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v_H_1351_);
lean_ctor_set(v___x_1454_, 1, v_a_1352_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg___boxed(lean_object* v_H_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_1456_, v_a_1457_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(lean_object* v_H_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_1460_, v_a_1461_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___boxed(lean_object* v_H_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(v_H_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
if (lean_obj_tag(v_a_1476_) == 0)
{
lean_object* v___x_1478_; 
v___x_1478_ = l_List_reverse___redArg(v_a_1477_);
return v___x_1478_;
}
else
{
lean_object* v_head_1479_; lean_object* v_tail_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1489_; 
v_head_1479_ = lean_ctor_get(v_a_1476_, 0);
v_tail_1480_ = lean_ctor_get(v_a_1476_, 1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1482_ = v_a_1476_;
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_tail_1480_);
lean_inc(v_head_1479_);
lean_dec(v_a_1476_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1484_ = l_Lean_MessageData_ofSyntax(v_head_1479_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 1, v_a_1477_);
lean_ctor_set(v___x_1482_, 0, v___x_1484_);
v___x_1486_ = v___x_1482_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_a_1477_);
v___x_1486_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v_a_1476_ = v_tail_1480_;
v_a_1477_ = v___x_1486_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0));
v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
return v___x_1492_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(lean_object* v_goal_1496_, lean_object* v_idents_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_u_1503_; lean_object* v_00_u03c3s_1504_; lean_object* v_hyps_1505_; lean_object* v_target_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_u_1503_ = lean_ctor_get(v_goal_1496_, 0);
v_00_u03c3s_1504_ = lean_ctor_get(v_goal_1496_, 1);
v_hyps_1505_ = lean_ctor_get(v_goal_1496_, 2);
v_target_1506_ = lean_ctor_get(v_goal_1496_, 3);
v___x_1507_ = l_Lean_NameSet_empty;
v___x_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
lean_ctor_set(v___x_1508_, 1, v_idents_1497_);
lean_inc_ref(v_hyps_1505_);
v___x_1509_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_hyps_1505_, v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1558_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1558_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1558_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v_fst_1514_; lean_object* v_snd_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1557_; 
v_fst_1514_ = lean_ctor_get(v_a_1510_, 0);
v_snd_1515_ = lean_ctor_get(v_a_1510_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_a_1510_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1517_ = v_a_1510_;
v_isShared_1518_ = v_isSharedCheck_1557_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_snd_1515_);
lean_inc(v_fst_1514_);
lean_dec(v_a_1510_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1557_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_snd_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1555_; 
v_snd_1524_ = lean_ctor_get(v_snd_1515_, 1);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_snd_1515_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v_snd_1515_, 0);
lean_dec(v_unused_1556_);
v___x_1526_ = v_snd_1515_;
v_isShared_1527_ = v_isSharedCheck_1555_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snd_1524_);
lean_dec(v_snd_1515_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1555_;
goto v_resetjp_1525_;
}
v___jp_1519_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1520_, 0, v_u_1503_);
lean_ctor_set(v___x_1520_, 1, v_00_u03c3s_1504_);
lean_ctor_set(v___x_1520_, 2, v_fst_1514_);
lean_ctor_set(v___x_1520_, 3, v_target_1506_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1520_);
v___x_1522_ = v___x_1512_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1528_ = lean_array_get_size(v_snd_1524_);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = lean_nat_dec_eq(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
lean_dec(v_fst_1514_);
lean_del_object(v___x_1512_);
v___x_1531_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1);
v___x_1532_ = lean_array_to_list(v_snd_1524_);
v___x_1533_ = lean_box(0);
v___x_1534_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(v___x_1532_, v___x_1533_);
v___x_1535_ = l_Lean_MessageData_ofList(v___x_1534_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 7);
lean_ctor_set(v___x_1526_, 1, v___x_1535_);
lean_ctor_set(v___x_1526_, 0, v___x_1531_);
v___x_1537_ = v___x_1526_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1538_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 7);
lean_ctor_set(v___x_1517_, 1, v___x_1538_);
lean_ctor_set(v___x_1517_, 0, v___x_1537_);
v___x_1540_ = v___x_1517_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
v___x_1541_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1496_);
v___x_1542_ = l_Lean_MessageData_ofExpr(v___x_1541_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1540_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1543_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
}
else
{
lean_inc_ref(v_target_1506_);
lean_inc_ref(v_00_u03c3s_1504_);
lean_inc(v_u_1503_);
lean_del_object(v___x_1526_);
lean_dec(v_snd_1524_);
lean_del_object(v___x_1517_);
lean_dec_ref(v_goal_1496_);
goto v___jp_1519_;
}
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_goal_1496_);
v_a_1559_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1509_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1509_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___boxed(lean_object* v_goal_1567_, lean_object* v_idents_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(v_goal_1567_, v_idents_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(lean_object* v_stx_1575_, lean_object* v_lctx_1576_, lean_object* v_expectedType_x3f_1577_, lean_object* v_expr_1578_, uint8_t v_isBinder_1579_, lean_object* v_x_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_stx_1575_);
v___x_1588_ = 0;
v___x_1589_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v_lctx_1576_);
lean_ctor_set(v___x_1589_, 2, v_expectedType_x3f_1577_);
lean_ctor_set(v___x_1589_, 3, v_expr_1578_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*4, v_isBinder_1579_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*4 + 1, v___x_1588_);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed(lean_object* v_stx_1593_, lean_object* v_lctx_1594_, lean_object* v_expectedType_x3f_1595_, lean_object* v_expr_1596_, lean_object* v_isBinder_1597_, lean_object* v_x_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v_isBinder_boxed_1604_; lean_object* v_res_1605_; 
v_isBinder_boxed_1604_ = lean_unbox(v_isBinder_1597_);
v_res_1605_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(v_stx_1593_, v_lctx_1594_, v_expectedType_x3f_1595_, v_expr_1596_, v_isBinder_boxed_1604_, v_x_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(lean_object* v___x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1606_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed(lean_object* v___x_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(v___x_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(lean_object* v___x_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1620_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed(lean_object* v___x_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(v___x_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1633_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = lean_unsigned_to_nat(32u);
v___x_1635_ = lean_mk_empty_array_with_capacity(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1637_ = ((size_t)5ULL);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_unsigned_to_nat(32u);
v___x_1640_ = lean_mk_empty_array_with_capacity(v___x_1639_);
v___x_1641_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0);
v___x_1642_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___x_1640_);
lean_ctor_set(v___x_1642_, 2, v___x_1638_);
lean_ctor_set(v___x_1642_, 3, v___x_1638_);
lean_ctor_set_usize(v___x_1642_, 4, v___x_1637_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1645_; lean_object* v_infoState_1646_; lean_object* v_trees_1647_; lean_object* v___x_1648_; lean_object* v_infoState_1649_; lean_object* v_env_1650_; lean_object* v_nextMacroScope_1651_; lean_object* v_ngen_1652_; lean_object* v_auxDeclNGen_1653_; lean_object* v_traceState_1654_; lean_object* v_cache_1655_; lean_object* v_recordedDeps_1656_; lean_object* v_messages_1657_; lean_object* v_snapshotTasks_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1679_; 
v___x_1645_ = lean_st_ref_get(v___y_1643_);
v_infoState_1646_ = lean_ctor_get(v___x_1645_, 8);
lean_inc_ref(v_infoState_1646_);
lean_dec(v___x_1645_);
v_trees_1647_ = lean_ctor_get(v_infoState_1646_, 2);
lean_inc_ref(v_trees_1647_);
lean_dec_ref(v_infoState_1646_);
v___x_1648_ = lean_st_ref_take(v___y_1643_);
v_infoState_1649_ = lean_ctor_get(v___x_1648_, 8);
v_env_1650_ = lean_ctor_get(v___x_1648_, 0);
v_nextMacroScope_1651_ = lean_ctor_get(v___x_1648_, 1);
v_ngen_1652_ = lean_ctor_get(v___x_1648_, 2);
v_auxDeclNGen_1653_ = lean_ctor_get(v___x_1648_, 3);
v_traceState_1654_ = lean_ctor_get(v___x_1648_, 4);
v_cache_1655_ = lean_ctor_get(v___x_1648_, 5);
v_recordedDeps_1656_ = lean_ctor_get(v___x_1648_, 6);
v_messages_1657_ = lean_ctor_get(v___x_1648_, 7);
v_snapshotTasks_1658_ = lean_ctor_get(v___x_1648_, 9);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1660_ = v___x_1648_;
v_isShared_1661_ = v_isSharedCheck_1679_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_snapshotTasks_1658_);
lean_inc(v_infoState_1649_);
lean_inc(v_messages_1657_);
lean_inc(v_recordedDeps_1656_);
lean_inc(v_cache_1655_);
lean_inc(v_traceState_1654_);
lean_inc(v_auxDeclNGen_1653_);
lean_inc(v_ngen_1652_);
lean_inc(v_nextMacroScope_1651_);
lean_inc(v_env_1650_);
lean_dec(v___x_1648_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1679_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
uint8_t v_enabled_1662_; lean_object* v_assignment_1663_; lean_object* v_lazyAssignment_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1677_; 
v_enabled_1662_ = lean_ctor_get_uint8(v_infoState_1649_, sizeof(void*)*3);
v_assignment_1663_ = lean_ctor_get(v_infoState_1649_, 0);
v_lazyAssignment_1664_ = lean_ctor_get(v_infoState_1649_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_infoState_1649_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_infoState_1649_, 2);
lean_dec(v_unused_1678_);
v___x_1666_ = v_infoState_1649_;
v_isShared_1667_ = v_isSharedCheck_1677_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_lazyAssignment_1664_);
lean_inc(v_assignment_1663_);
lean_dec(v_infoState_1649_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1677_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 2, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_assignment_1663_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_lazyAssignment_1664_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v___x_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*3, v_enabled_1662_);
v___x_1670_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 8, v___x_1670_);
v___x_1672_ = v___x_1660_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_env_1650_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_nextMacroScope_1651_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_ngen_1652_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_auxDeclNGen_1653_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_traceState_1654_);
lean_ctor_set(v_reuseFailAlloc_1675_, 5, v_cache_1655_);
lean_ctor_set(v_reuseFailAlloc_1675_, 6, v_recordedDeps_1656_);
lean_ctor_set(v_reuseFailAlloc_1675_, 7, v_messages_1657_);
lean_ctor_set(v_reuseFailAlloc_1675_, 8, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1675_, 9, v_snapshotTasks_1658_);
v___x_1672_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_st_ref_put(v___y_1643_, v___x_1672_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_trees_1647_);
return v___x_1674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___boxed(lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1680_);
lean_dec(v___y_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(lean_object* v_mkInfoOnError_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___f_1688_, lean_object* v_mkInfo_1689_, lean_object* v_a_x3f_1690_){
_start:
{
if (lean_obj_tag(v_a_x3f_1690_) == 0)
{
lean_object* v___x_1692_; 
lean_dec_ref(v_mkInfo_1689_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1692_ = lean_apply_5(v_mkInfoOnError_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_a_1693_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1695_ = lean_apply_6(v___f_1688_, v___x_1694_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
return v___x_1695_;
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v___f_1688_);
v_a_1696_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1692_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1692_);
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
else
{
lean_object* v_val_1704_; lean_object* v___x_1705_; 
lean_dec_ref(v_mkInfoOnError_1683_);
v_val_1704_ = lean_ctor_get(v_a_x3f_1690_, 0);
lean_inc(v_val_1704_);
lean_dec_ref_known(v_a_x3f_1690_, 1);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1705_ = lean_apply_6(v_mkInfo_1689_, v_val_1704_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1707_ = lean_apply_6(v___f_1688_, v_a_1706_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, lean_box(0));
return v___x_1707_;
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec_ref(v___f_1688_);
v_a_1708_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1705_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1705_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1___boxed(lean_object* v_mkInfoOnError_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___f_1721_, lean_object* v_mkInfo_1722_, lean_object* v_a_x3f_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___f_1721_, v_mkInfo_1722_, v_a_x3f_1723_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(lean_object* v_a_1726_, lean_object* v_info_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_infoState_1734_; lean_object* v_env_1735_; lean_object* v_nextMacroScope_1736_; lean_object* v_ngen_1737_; lean_object* v_auxDeclNGen_1738_; lean_object* v_traceState_1739_; lean_object* v_cache_1740_; lean_object* v_recordedDeps_1741_; lean_object* v_messages_1742_; lean_object* v_snapshotTasks_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1781_; 
v___x_1733_ = lean_st_ref_take(v___y_1731_);
v_infoState_1734_ = lean_ctor_get(v___x_1733_, 8);
v_env_1735_ = lean_ctor_get(v___x_1733_, 0);
v_nextMacroScope_1736_ = lean_ctor_get(v___x_1733_, 1);
v_ngen_1737_ = lean_ctor_get(v___x_1733_, 2);
v_auxDeclNGen_1738_ = lean_ctor_get(v___x_1733_, 3);
v_traceState_1739_ = lean_ctor_get(v___x_1733_, 4);
v_cache_1740_ = lean_ctor_get(v___x_1733_, 5);
v_recordedDeps_1741_ = lean_ctor_get(v___x_1733_, 6);
v_messages_1742_ = lean_ctor_get(v___x_1733_, 7);
v_snapshotTasks_1743_ = lean_ctor_get(v___x_1733_, 9);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1745_ = v___x_1733_;
v_isShared_1746_ = v_isSharedCheck_1781_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_snapshotTasks_1743_);
lean_inc(v_infoState_1734_);
lean_inc(v_messages_1742_);
lean_inc(v_recordedDeps_1741_);
lean_inc(v_cache_1740_);
lean_inc(v_traceState_1739_);
lean_inc(v_auxDeclNGen_1738_);
lean_inc(v_ngen_1737_);
lean_inc(v_nextMacroScope_1736_);
lean_inc(v_env_1735_);
lean_dec(v___x_1733_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1781_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
uint8_t v_enabled_1747_; lean_object* v_assignment_1748_; lean_object* v_lazyAssignment_1749_; lean_object* v_trees_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1780_; 
v_enabled_1747_ = lean_ctor_get_uint8(v_infoState_1734_, sizeof(void*)*3);
v_assignment_1748_ = lean_ctor_get(v_infoState_1734_, 0);
v_lazyAssignment_1749_ = lean_ctor_get(v_infoState_1734_, 1);
v_trees_1750_ = lean_ctor_get(v_infoState_1734_, 2);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_infoState_1734_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1752_ = v_infoState_1734_;
v_isShared_1753_ = v_isSharedCheck_1780_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_trees_1750_);
lean_inc(v_lazyAssignment_1749_);
lean_inc(v_assignment_1748_);
lean_dec(v_infoState_1734_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1780_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___y_1756_; 
v___x_1754_ = lean_box(0);
if (lean_obj_tag(v_info_1727_) == 0)
{
lean_object* v_val_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v_val_1762_ = lean_ctor_get(v_info_1727_, 0);
lean_inc(v_val_1762_);
lean_dec_ref_known(v_info_1727_, 1);
v___x_1763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1763_, 0, v_val_1762_);
lean_ctor_set(v___x_1763_, 1, v_trees_1750_);
v___x_1764_ = l_Lean_PersistentArray_push___redArg(v_a_1726_, v___x_1763_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 2, v___x_1764_);
v___x_1766_ = v___x_1752_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_assignment_1748_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_lazyAssignment_1749_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v___x_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1767_, sizeof(void*)*3, v_enabled_1747_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
v___y_1756_ = v___x_1766_;
goto v___jp_1755_;
}
}
else
{
lean_object* v_val_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v_trees_1750_);
v_val_1768_ = lean_ctor_get(v_info_1727_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_info_1727_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1770_ = v_info_1727_;
v_isShared_1771_ = v_isSharedCheck_1779_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_val_1768_);
lean_dec(v_info_1727_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1779_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 2);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_val_1768_);
v___x_1773_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = l_Lean_PersistentArray_push___redArg(v_a_1726_, v___x_1773_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 2, v___x_1774_);
v___x_1776_ = v___x_1752_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_assignment_1748_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_lazyAssignment_1749_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v___x_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1777_, sizeof(void*)*3, v_enabled_1747_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
v___y_1756_ = v___x_1776_;
goto v___jp_1755_;
}
}
}
}
v___jp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 8, v___y_1756_);
v___x_1758_ = v___x_1745_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_env_1735_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_nextMacroScope_1736_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_ngen_1737_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_auxDeclNGen_1738_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_traceState_1739_);
lean_ctor_set(v_reuseFailAlloc_1761_, 5, v_cache_1740_);
lean_ctor_set(v_reuseFailAlloc_1761_, 6, v_recordedDeps_1741_);
lean_ctor_set(v_reuseFailAlloc_1761_, 7, v_messages_1742_);
lean_ctor_set(v_reuseFailAlloc_1761_, 8, v___y_1756_);
lean_ctor_set(v_reuseFailAlloc_1761_, 9, v_snapshotTasks_1743_);
v___x_1758_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_st_ref_put(v___y_1731_, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1754_);
return v___x_1760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed(lean_object* v_a_1782_, lean_object* v_info_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(v_a_1782_, v_info_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(lean_object* v_x_1790_, lean_object* v_mkInfo_1791_, lean_object* v_mkInfoOnError_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_infoState_1799_; uint8_t v_enabled_1800_; 
v___x_1798_ = lean_st_ref_get(v___y_1796_);
v_infoState_1799_ = lean_ctor_get(v___x_1798_, 8);
lean_inc_ref(v_infoState_1799_);
lean_dec(v___x_1798_);
v_enabled_1800_ = lean_ctor_get_uint8(v_infoState_1799_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1799_);
if (v_enabled_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v_mkInfoOnError_1792_);
lean_dec_ref(v_mkInfo_1791_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
v___x_1801_ = lean_apply_5(v_x_1790_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, lean_box(0));
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v_a_1803_; lean_object* v___f_1804_; lean_object* v_r_1805_; 
v___x_1802_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1796_);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1804_, 0, v_a_1803_);
lean_inc(v___y_1796_);
lean_inc_ref(v___y_1795_);
lean_inc(v___y_1794_);
lean_inc_ref(v___y_1793_);
v_r_1805_ = lean_apply_5(v_x_1790_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, lean_box(0));
if (lean_obj_tag(v_r_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1830_; 
v_a_1806_ = lean_ctor_get(v_r_1805_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_r_1805_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1808_ = v_r_1805_;
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v_r_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1830_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
lean_inc(v_a_1806_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set_tag(v___x_1808_, 1);
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___f_1804_, v_mkInfo_1791_, v___x_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1812_, 0);
lean_dec(v_unused_1820_);
v___x_1814_ = v___x_1812_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v___x_1812_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v_a_1806_);
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1806_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_a_1806_);
v_a_1821_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1812_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1812_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_a_1831_ = lean_ctor_get(v_r_1805_, 0);
lean_inc(v_a_1831_);
lean_dec_ref_known(v_r_1805_, 1);
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___f_1804_, v_mkInfo_1791_, v___x_1832_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; 
v_unused_1841_ = lean_ctor_get(v___x_1833_, 0);
lean_dec(v_unused_1841_);
v___x_1835_ = v___x_1833_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_dec(v___x_1833_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 1);
lean_ctor_set(v___x_1835_, 0, v_a_1831_);
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1831_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
lean_dec(v_a_1831_);
v_a_1842_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1844_ = v___x_1833_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1833_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_a_1842_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___boxed(lean_object* v_x_1850_, lean_object* v_mkInfo_1851_, lean_object* v_mkInfoOnError_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_1850_, v_mkInfo_1851_, v_mkInfoOnError_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object* v_stx_1861_, lean_object* v_lctx_1862_, lean_object* v_expr_1863_, lean_object* v_expectedType_x3f_1864_, uint8_t v_isBinder_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v___f_1872_; lean_object* v___f_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___f_1878_; lean_object* v___x_1879_; 
v___x_1871_ = lean_box(v_isBinder_1865_);
lean_inc(v_expectedType_x3f_1864_);
lean_inc_ref(v_lctx_1862_);
lean_inc(v_stx_1861_);
v___f_1872_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1872_, 0, v_stx_1861_);
lean_closure_set(v___f_1872_, 1, v_lctx_1862_);
lean_closure_set(v___f_1872_, 2, v_expectedType_x3f_1864_);
lean_closure_set(v___f_1872_, 3, v_expr_1863_);
lean_closure_set(v___f_1872_, 4, v___x_1871_);
v___f_1873_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0));
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_stx_1861_);
v___x_1876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v_lctx_1862_);
lean_ctor_set(v___x_1876_, 2, v_expectedType_x3f_1864_);
v___x_1877_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
v___f_1878_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1878_, 0, v___x_1877_);
v___x_1879_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v___f_1873_, v___f_1872_, v___f_1878_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed(lean_object* v_stx_1880_, lean_object* v_lctx_1881_, lean_object* v_expr_1882_, lean_object* v_expectedType_x3f_1883_, lean_object* v_isBinder_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
uint8_t v_isBinder_boxed_1890_; lean_object* v_res_1891_; 
v_isBinder_boxed_1890_ = lean_unbox(v_isBinder_1884_);
v_res_1891_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_stx_1880_, v_lctx_1881_, v_expr_1882_, v_expectedType_x3f_1883_, v_isBinder_boxed_1890_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1895_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___boxed(lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(lean_object* v_00_u03b1_1904_, lean_object* v_x_1905_, lean_object* v_mkInfo_1906_, lean_object* v_mkInfoOnError_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_1905_, v_mkInfo_1906_, v_mkInfoOnError_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___boxed(lean_object* v_00_u03b1_1914_, lean_object* v_x_1915_, lean_object* v_mkInfo_1916_, lean_object* v_mkInfoOnError_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(v_00_u03b1_1914_, v_x_1915_, v_mkInfo_1916_, v_mkInfoOnError_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object* v_stx_1930_, lean_object* v_00_u03c3s_1931_, lean_object* v_hyp_1932_, uint8_t v_isBinder_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_lctx_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_lctx_1939_ = lean_ctor_get(v_a_1934_, 2);
v___x_1940_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1));
v___x_1941_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_1940_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_name_1943_; lean_object* v_uniq_1944_; lean_object* v_p_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v_name_1943_ = lean_ctor_get(v_hyp_1932_, 0);
lean_inc(v_name_1943_);
v_uniq_1944_ = lean_ctor_get(v_hyp_1932_, 1);
lean_inc_n(v_uniq_1944_, 2);
v_p_1945_ = lean_ctor_get(v_hyp_1932_, 2);
lean_inc_ref(v_p_1945_);
lean_dec_ref(v_hyp_1932_);
v___x_1946_ = l_Lean_mkAppB(v_a_1942_, v_00_u03c3s_1931_, v_p_1945_);
v___x_1947_ = 0;
v___x_1948_ = 0;
lean_inc_ref(v___x_1946_);
lean_inc_ref(v_lctx_1939_);
v___x_1949_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1939_, v_uniq_1944_, v_name_1943_, v___x_1946_, v___x_1947_, v___x_1948_);
v___x_1950_ = l_Lean_Expr_fvar___override(v_uniq_1944_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1946_);
v___x_1952_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_stx_1930_, v___x_1949_, v___x_1950_, v___x_1951_, v_isBinder_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
return v___x_1952_;
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_hyp_1932_);
lean_dec_ref(v_00_u03c3s_1931_);
lean_dec(v_stx_1930_);
v_a_1953_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1941_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1941_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed(lean_object* v_stx_1961_, lean_object* v_00_u03c3s_1962_, lean_object* v_hyp_1963_, lean_object* v_isBinder_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_){
_start:
{
uint8_t v_isBinder_boxed_1970_; lean_object* v_res_1971_; 
v_isBinder_boxed_1970_ = lean_unbox(v_isBinder_1964_);
v_res_1971_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_stx_1961_, v_00_u03c3s_1962_, v_hyp_1963_, v_isBinder_boxed_1970_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
return v_res_1971_;
}
}
lean_object* runtime_initialize_Std_Do_SPred_DerivedLaws(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_ProofMode(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Do_SPred_DerivedLaws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_ProofMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default = _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default);
l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal = _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_SPred_DerivedLaws(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_ProofMode(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred_DerivedLaws(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_ProofMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
}
#ifdef __cplusplus
}
#endif
