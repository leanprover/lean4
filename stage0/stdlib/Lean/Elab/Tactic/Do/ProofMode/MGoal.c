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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_x_9_);
v_tail_15_ = lean_ctor_get(v_data_10_, 1);
lean_inc(v_tail_15_);
lean_dec_ref(v_data_10_);
v_snd_16_ = lean_ctor_get(v_head_11_, 1);
lean_inc(v_snd_16_);
lean_dec(v_head_11_);
v_str_17_ = lean_ctor_get(v_fst_12_, 1);
lean_inc_ref(v_str_17_);
lean_dec_ref(v_fst_12_);
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
lean_dec_ref(v_snd_16_);
v_tail_25_ = lean_ctor_get(v_tail_15_, 1);
lean_inc(v_tail_25_);
lean_dec_ref(v_tail_15_);
v_snd_26_ = lean_ctor_get(v_head_21_, 1);
lean_inc(v_snd_26_);
lean_dec(v_head_21_);
v_str_27_ = lean_ctor_get(v_fst_22_, 1);
lean_inc_ref(v_str_27_);
lean_dec_ref(v_fst_22_);
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
lean_dec_ref(v_snd_26_);
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
lean_dec_ref(v_fst_22_);
lean_dec(v_head_21_);
lean_dec_ref(v_tail_15_);
lean_dec_ref(v_snd_16_);
lean_dec_ref(v_expr_14_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
}
else
{
lean_object* v___x_43_; 
lean_dec(v_fst_22_);
lean_dec(v_head_21_);
lean_dec_ref(v_tail_15_);
lean_dec_ref(v_snd_16_);
lean_dec_ref(v_expr_14_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
}
else
{
lean_object* v___x_44_; 
lean_dec_ref(v_snd_16_);
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
lean_dec_ref(v_fst_12_);
lean_dec(v_head_11_);
lean_dec_ref(v_data_10_);
lean_dec_ref(v_x_9_);
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
else
{
lean_object* v___x_47_; 
lean_dec(v_fst_12_);
lean_dec(v_head_11_);
lean_dec_ref(v_data_10_);
lean_dec_ref(v_x_9_);
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
else
{
lean_object* v___x_48_; 
lean_dec_ref(v_x_9_);
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
lean_dec_ref(v_x_92_);
v_arg_101_ = lean_ctor_get(v_fn_93_, 1);
lean_inc_ref(v_arg_101_);
lean_dec_ref(v_fn_93_);
v_us_102_ = lean_ctor_get(v_fn_94_, 1);
lean_inc(v_us_102_);
lean_dec_ref(v_fn_94_);
v_str_103_ = lean_ctor_get(v_declName_95_, 1);
lean_inc_ref(v_str_103_);
lean_dec_ref(v_declName_95_);
v_str_104_ = lean_ctor_get(v_pre_96_, 1);
lean_inc_ref(v_str_104_);
lean_dec_ref(v_pre_96_);
v_str_105_ = lean_ctor_get(v_pre_97_, 1);
lean_inc_ref(v_str_105_);
lean_dec_ref(v_pre_97_);
v_str_106_ = lean_ctor_get(v_pre_98_, 1);
lean_inc_ref(v_str_106_);
lean_dec_ref(v_pre_98_);
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
lean_dec_ref(v_us_102_);
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
lean_dec_ref(v_pre_98_);
lean_dec_ref(v_pre_97_);
lean_dec_ref(v_pre_96_);
lean_dec_ref(v_declName_95_);
lean_dec_ref(v_fn_94_);
lean_dec_ref(v_fn_93_);
lean_dec_ref(v_x_92_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
}
else
{
lean_object* v___x_134_; 
lean_dec_ref(v_pre_97_);
lean_dec(v_pre_98_);
lean_dec_ref(v_pre_96_);
lean_dec_ref(v_declName_95_);
lean_dec_ref(v_fn_94_);
lean_dec_ref(v_fn_93_);
lean_dec_ref(v_x_92_);
v___x_134_ = lean_box(0);
return v___x_134_;
}
}
else
{
lean_object* v___x_135_; 
lean_dec(v_pre_97_);
lean_dec_ref(v_pre_96_);
lean_dec_ref(v_declName_95_);
lean_dec_ref(v_fn_94_);
lean_dec_ref(v_fn_93_);
lean_dec_ref(v_x_92_);
v___x_135_ = lean_box(0);
return v___x_135_;
}
}
else
{
lean_object* v___x_136_; 
lean_dec(v_pre_96_);
lean_dec_ref(v_declName_95_);
lean_dec_ref(v_fn_94_);
lean_dec_ref(v_fn_93_);
lean_dec_ref(v_x_92_);
v___x_136_ = lean_box(0);
return v___x_136_;
}
}
else
{
lean_object* v___x_137_; 
lean_dec_ref(v_fn_94_);
lean_dec(v_declName_95_);
lean_dec_ref(v_fn_93_);
lean_dec_ref(v_x_92_);
v___x_137_ = lean_box(0);
return v___x_137_;
}
}
else
{
lean_object* v___x_138_; 
lean_dec_ref(v_fn_94_);
lean_dec_ref(v_fn_93_);
lean_dec_ref(v_x_92_);
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
else
{
lean_object* v___x_139_; 
lean_dec_ref(v_x_92_);
lean_dec_ref(v_fn_93_);
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
lean_object* v_val_161_; lean_object* v_name_162_; lean_object* v_p_163_; uint8_t v___y_165_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_val_161_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_val_161_);
lean_dec_ref(v___x_159_);
v_name_162_ = lean_ctor_get(v_val_161_, 0);
lean_inc(v_name_162_);
v_p_163_ = lean_ctor_get(v_val_161_, 2);
lean_inc_ref(v_p_163_);
lean_dec(v_val_161_);
v___x_198_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName));
v___x_199_ = lean_name_eq(v_name_162_, v___x_198_);
if (v___x_199_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = l_Lean_Name_hasMacroScopes(v_name_162_);
lean_dec(v_name_162_);
v___y_165_ = v___x_200_;
goto v___jp_164_;
}
else
{
lean_dec(v_name_162_);
v___y_165_ = v___x_199_;
goto v___jp_164_;
}
v___jp_164_:
{
if (v___y_165_ == 0)
{
lean_object* v___x_166_; 
lean_dec_ref(v_p_163_);
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(v_p_163_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v_val_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_197_; 
v_val_169_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_197_ == 0)
{
v___x_171_ = v___x_167_;
v_isShared_172_ = v_isSharedCheck_197_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_val_169_);
lean_dec(v___x_167_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_197_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_snd_173_; lean_object* v_snd_174_; 
v_snd_173_ = lean_ctor_get(v_val_169_, 1);
lean_inc(v_snd_173_);
v_snd_174_ = lean_ctor_get(v_snd_173_, 1);
if (lean_obj_tag(v_snd_174_) == 4)
{
lean_object* v_declName_175_; 
v_declName_175_ = lean_ctor_get(v_snd_174_, 0);
lean_inc(v_declName_175_);
if (lean_obj_tag(v_declName_175_) == 1)
{
lean_object* v_pre_176_; 
v_pre_176_ = lean_ctor_get(v_declName_175_, 0);
if (lean_obj_tag(v_pre_176_) == 0)
{
lean_object* v_fst_177_; lean_object* v_fst_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_192_; 
v_fst_177_ = lean_ctor_get(v_val_169_, 0);
lean_inc(v_fst_177_);
lean_dec(v_val_169_);
v_fst_178_ = lean_ctor_get(v_snd_173_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v_snd_173_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; 
v_unused_193_ = lean_ctor_get(v_snd_173_, 1);
lean_dec(v_unused_193_);
v___x_180_ = v_snd_173_;
v_isShared_181_ = v_isSharedCheck_192_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_fst_178_);
lean_dec(v_snd_173_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_192_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_str_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_str_182_ = lean_ctor_get(v_declName_175_, 1);
lean_inc_ref(v_str_182_);
lean_dec_ref(v_declName_175_);
v___x_183_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0));
v___x_184_ = lean_string_dec_eq(v_str_182_, v___x_183_);
lean_dec_ref(v_str_182_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
lean_del_object(v___x_180_);
lean_dec(v_fst_178_);
lean_dec(v_fst_177_);
lean_del_object(v___x_171_);
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v___x_187_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v_fst_178_);
lean_ctor_set(v___x_180_, 0, v_fst_177_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_fst_177_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_fst_178_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_187_);
v___x_189_ = v___x_171_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v___x_194_; 
lean_dec_ref(v_declName_175_);
lean_dec(v_snd_173_);
lean_del_object(v___x_171_);
lean_dec(v_val_169_);
v___x_194_ = lean_box(0);
return v___x_194_;
}
}
else
{
lean_object* v___x_195_; 
lean_dec(v_declName_175_);
lean_dec(v_snd_173_);
lean_del_object(v___x_171_);
lean_dec(v_val_169_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v_snd_173_);
lean_del_object(v___x_171_);
lean_dec(v_val_169_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(lean_object* v_pos_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(3u);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_202_, v___x_203_, v_pos_201_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct___boxed(lean_object* v_pos_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_pos_205_);
lean_dec(v_pos_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(lean_object* v_pos_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(3u);
v___x_209_ = lean_unsigned_to_nat(2u);
v___x_210_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_208_, v___x_209_, v_pos_207_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct___boxed(lean_object* v_pos_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_pos_211_);
lean_dec(v_pos_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object* v_u_219_, lean_object* v_00_u03c3s_220_, lean_object* v_lhs_221_, lean_object* v_rhs_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1));
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v_u_219_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = l_Lean_mkConst(v___x_223_, v___x_225_);
v___x_227_ = l_Lean_mkApp3(v___x_226_, v_00_u03c3s_220_, v_lhs_221_, v_rhs_222_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object* v_u_248_, lean_object* v_00_u03c3s_249_, lean_object* v_lhs_250_, lean_object* v_rhs_251_){
_start:
{
lean_object* v___x_252_; 
lean_inc_ref(v_lhs_250_);
v___x_252_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_lhs_250_);
if (lean_obj_tag(v___x_252_) == 1)
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v___x_252_);
lean_dec_ref(v_lhs_250_);
v___x_253_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1));
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v_u_248_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = l_Lean_mkConst(v___x_253_, v___x_255_);
lean_inc_ref(v_rhs_251_);
v___x_257_ = l_Lean_mkAppB(v___x_256_, v_00_u03c3s_249_, v_rhs_251_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v_rhs_251_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
return v___x_258_;
}
else
{
lean_object* v___x_259_; 
lean_dec(v___x_252_);
lean_inc_ref(v_rhs_251_);
v___x_259_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_rhs_251_);
if (lean_obj_tag(v___x_259_) == 1)
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref(v___x_259_);
lean_dec_ref(v_rhs_251_);
v___x_260_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3));
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_262_, 0, v_u_248_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_Lean_mkConst(v___x_260_, v___x_262_);
lean_inc_ref(v_lhs_250_);
v___x_264_ = l_Lean_mkAppB(v___x_263_, v_00_u03c3s_249_, v_lhs_250_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_lhs_250_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
return v___x_265_;
}
else
{
lean_object* v_result_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_259_);
lean_inc_ref(v_00_u03c3s_249_);
lean_inc(v_u_248_);
v_result_266_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_248_, v_00_u03c3s_249_, v_lhs_250_, v_rhs_251_);
v___x_267_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6));
v___x_268_ = lean_box(0);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v_u_248_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_mkConst(v___x_267_, v___x_269_);
lean_inc_ref(v_result_266_);
v___x_271_ = l_Lean_mkAppB(v___x_270_, v_00_u03c3s_249_, v_result_266_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_result_266_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(lean_object* v_u_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1));
v___x_278_ = l_Lean_Level_succ___override(v_u_276_);
v___x_279_ = lean_box(0);
lean_inc(v___x_278_);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Lean_mkConst(v___x_277_, v___x_280_);
v___x_282_ = l_Lean_mkSort(v___x_278_);
v___x_283_ = l_Lean_Expr_app___override(v___x_281_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(lean_object* v_u_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_289_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1));
v___x_290_ = l_Lean_Level_succ___override(v_u_288_);
v___x_291_ = lean_box(0);
lean_inc(v___x_290_);
v___x_292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = l_Lean_mkConst(v___x_289_, v___x_292_);
v___x_294_ = l_Lean_mkSort(v___x_290_);
v___x_295_ = l_Lean_Expr_app___override(v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(lean_object* v_u_300_, lean_object* v_hd_301_, lean_object* v_tl_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1));
v___x_304_ = l_Lean_Level_succ___override(v_u_300_);
v___x_305_ = lean_box(0);
lean_inc(v___x_304_);
v___x_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = l_Lean_mkConst(v___x_303_, v___x_306_);
v___x_308_ = l_Lean_mkSort(v___x_304_);
v___x_309_ = l_Lean_mkApp3(v___x_307_, v___x_308_, v_hd_301_, v_tl_302_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(lean_object* v_b_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_fst_316_; lean_object* v_snd_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_349_; 
v_fst_316_ = lean_ctor_get(v_b_310_, 0);
v_snd_317_ = lean_ctor_get(v_b_310_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_b_310_);
if (v_isSharedCheck_349_ == 0)
{
v___x_319_ = v_b_310_;
v_isShared_320_ = v_isSharedCheck_349_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_snd_317_);
lean_inc(v_fst_316_);
lean_dec(v_b_310_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_349_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1));
v___x_322_ = lean_unsigned_to_nat(3u);
v___x_323_ = l_Lean_Expr_isAppOfArity(v_fst_316_, v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_325_; 
if (v_isShared_320_ == 0)
{
v___x_325_ = v___x_319_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_fst_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_snd_317_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; 
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_328_ = lean_unsigned_to_nat(2u);
v___x_329_ = l_Lean_Expr_getAppNumArgs(v_fst_316_);
v___x_330_ = lean_nat_sub(v___x_329_, v___x_328_);
lean_dec(v___x_329_);
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_sub(v___x_330_, v___x_331_);
lean_dec(v___x_330_);
v___x_333_ = l_Lean_Expr_getRevArg_x21(v_fst_316_, v___x_332_);
lean_dec(v_fst_316_);
v___x_334_ = l_Lean_Meta_whnfR(v___x_333_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref(v___x_334_);
v___x_336_ = lean_nat_add(v_snd_317_, v___x_331_);
lean_dec(v_snd_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v___x_336_);
lean_ctor_set(v___x_319_, 0, v_a_335_);
v___x_338_ = v___x_319_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_335_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
v_b_310_ = v___x_338_;
goto _start;
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_del_object(v___x_319_);
lean_dec(v_snd_317_);
v_a_341_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_334_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_334_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___boxed(lean_object* v_b_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(v_b_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(lean_object* v_00_u03c3s_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_whnfR(v_00_u03c3s_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref(v___x_363_);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_a_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(v___x_366_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_376_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_376_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_376_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v_snd_372_; lean_object* v___x_374_; 
v_snd_372_ = lean_ctor_get(v_a_368_, 1);
lean_inc(v_snd_372_);
lean_dec(v_a_368_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v_snd_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_snd_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
v_a_377_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_367_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_367_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_363_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_363_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length___boxed(lean_object* v_00_u03c3s_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(v_00_u03c3s_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object* v_e_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1));
v___x_402_ = lean_unsigned_to_nat(3u);
v___x_403_ = l_Lean_Expr_isAppOfArity(v_e_400_, v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_box(0);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_405_ = lean_box(0);
v___x_406_ = l_Lean_Expr_appFn_x21(v_e_400_);
v___x_407_ = l_Lean_Expr_appFn_x21(v___x_406_);
v___x_408_ = l_Lean_Expr_appArg_x21(v___x_407_);
lean_dec_ref(v___x_407_);
v___x_409_ = l_Lean_Expr_appArg_x21(v___x_406_);
lean_dec_ref(v___x_406_);
v___x_410_ = l_Lean_Expr_appArg_x21(v_e_400_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_409_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_408_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_Expr_getAppFn(v_e_400_);
v___x_414_ = l_Lean_Expr_constLevels_x21(v___x_413_);
lean_dec_ref(v___x_413_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = l_List_get_x21Internal___redArg(v___x_405_, v___x_414_, v___x_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_412_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f___boxed(lean_object* v_e_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_419_);
lean_dec_ref(v_e_419_);
return v_res_420_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_box(0);
v___x_425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1));
v___x_426_ = l_Lean_Expr_const___override(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_427_);
lean_ctor_set(v___x_429_, 3, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal(void){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default;
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object* v_expr_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_440_ = l_Lean_Expr_consumeMData(v_expr_439_);
v___x_441_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2));
v___x_442_ = lean_unsigned_to_nat(3u);
v___x_443_ = l_Lean_Expr_isAppOfArity(v___x_440_, v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; 
lean_dec_ref(v___x_440_);
v___x_444_ = lean_box(0);
return v___x_444_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_445_ = lean_box(0);
v___x_446_ = l_Lean_Expr_appFn_x21(v___x_440_);
v___x_447_ = l_Lean_Expr_appFn_x21(v___x_446_);
v___x_448_ = l_Lean_Expr_appArg_x21(v___x_447_);
lean_dec_ref(v___x_447_);
v___x_449_ = l_Lean_Expr_appArg_x21(v___x_446_);
lean_dec_ref(v___x_446_);
v___x_450_ = l_Lean_Expr_appArg_x21(v___x_440_);
lean_dec_ref(v___x_440_);
v___x_451_ = l_Lean_Expr_getAppFn_x27(v_expr_439_);
v___x_452_ = l_Lean_Expr_constLevels_x21(v___x_451_);
lean_dec_ref(v___x_451_);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = l_List_get_x21Internal___redArg(v___x_445_, v___x_452_, v___x_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_448_);
lean_ctor_set(v___x_455_, 2, v___x_449_);
lean_ctor_set(v___x_455_, 3, v___x_450_);
v___x_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___boxed(lean_object* v_expr_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_expr_457_);
lean_dec_ref(v_expr_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(lean_object* v_e_459_, lean_object* v___y_460_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_Lean_Expr_hasMVar(v_e_459_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_e_459_);
return v___x_463_;
}
else
{
lean_object* v___x_464_; lean_object* v_mctx_465_; lean_object* v___x_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___x_469_; lean_object* v_cache_470_; lean_object* v_zetaDeltaFVarIds_471_; lean_object* v_postponed_472_; lean_object* v_diag_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
v___x_464_ = lean_st_ref_get(v___y_460_);
v_mctx_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_ref(v_mctx_465_);
lean_dec(v___x_464_);
v___x_466_ = l_Lean_instantiateMVarsCore(v_mctx_465_, v_e_459_);
v_fst_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v___x_466_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v___x_466_);
v___x_469_ = lean_st_ref_take(v___y_460_);
v_cache_470_ = lean_ctor_get(v___x_469_, 1);
v_zetaDeltaFVarIds_471_ = lean_ctor_get(v___x_469_, 2);
v_postponed_472_ = lean_ctor_get(v___x_469_, 3);
v_diag_473_ = lean_ctor_get(v___x_469_, 4);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_469_, 0);
lean_dec(v_unused_483_);
v___x_475_ = v___x_469_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_diag_473_);
lean_inc(v_postponed_472_);
lean_inc(v_zetaDeltaFVarIds_471_);
lean_inc(v_cache_470_);
lean_dec(v___x_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v_snd_468_);
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_snd_468_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_cache_470_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_zetaDeltaFVarIds_471_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_postponed_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_diag_473_);
v___x_478_ = v_reuseFailAlloc_481_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_st_ref_set(v___y_460_, v___x_478_);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v_fst_467_);
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg___boxed(lean_object* v_e_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_e_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(lean_object* v_e_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_e_488_, v___y_494_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___boxed(lean_object* v_e_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(v_e_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(lean_object* v_msgData_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; lean_object* v_env_517_; lean_object* v___x_518_; lean_object* v_mctx_519_; lean_object* v_lctx_520_; lean_object* v_options_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_516_ = lean_st_ref_get(v___y_514_);
v_env_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc_ref(v_env_517_);
lean_dec(v___x_516_);
v___x_518_ = lean_st_ref_get(v___y_512_);
v_mctx_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc_ref(v_mctx_519_);
lean_dec(v___x_518_);
v_lctx_520_ = lean_ctor_get(v___y_511_, 2);
v_options_521_ = lean_ctor_get(v___y_513_, 2);
lean_inc_ref(v_options_521_);
lean_inc_ref(v_lctx_520_);
v___x_522_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_522_, 0, v_env_517_);
lean_ctor_set(v___x_522_, 1, v_mctx_519_);
lean_ctor_set(v___x_522_, 2, v_lctx_520_);
lean_ctor_set(v___x_522_, 3, v_options_521_);
v___x_523_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_msgData_510_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1___boxed(lean_object* v_msgData_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msgData_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(lean_object* v_msg_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_ref_538_; lean_object* v___x_539_; lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
v_ref_538_ = lean_ctor_get(v___y_535_, 5);
v___x_539_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_548_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
lean_inc(v_ref_538_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_ref_538_);
lean_ctor_set(v___x_544_, 1, v_a_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 1);
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg___boxed(lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
return v_res_555_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0));
v___x_558_ = l_Lean_stringToMessageData(v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_560_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_n(v_a_569_, 2);
lean_dec_ref(v___x_568_);
v___x_570_ = l_Lean_MVarId_getType(v_a_569_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_585_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
v___x_572_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_a_571_, v_a_564_);
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_585_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_585_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_573_);
lean_dec(v_a_573_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_val_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v_val_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_578_);
lean_dec_ref(v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v_a_569_);
lean_ctor_set(v___x_579_, 1, v_val_578_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_579_);
v___x_581_ = v___x_575_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec(v___x_577_);
lean_del_object(v___x_575_);
lean_dec(v_a_569_);
v___x_583_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1);
v___x_584_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v___x_583_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
return v___x_584_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_569_);
v_a_586_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_570_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_570_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
v_a_594_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_568_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_568_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___boxed(lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(lean_object* v_00_u03b1_612_, lean_object* v_msg_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v_msg_613_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___boxed(lean_object* v_00_u03b1_624_, lean_object* v_msg_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(v_00_u03b1_624_, v_msg_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(lean_object* v_goal_642_){
_start:
{
lean_object* v_u_643_; lean_object* v_00_u03c3s_644_; lean_object* v_hyps_645_; lean_object* v_target_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_u_643_ = lean_ctor_get(v_goal_642_, 0);
lean_inc(v_u_643_);
v_00_u03c3s_644_ = lean_ctor_get(v_goal_642_, 1);
lean_inc_ref(v_00_u03c3s_644_);
v_hyps_645_ = lean_ctor_get(v_goal_642_, 2);
lean_inc_ref(v_hyps_645_);
v_target_646_ = lean_ctor_get(v_goal_642_, 3);
lean_inc_ref(v_target_646_);
lean_dec_ref(v_goal_642_);
v___x_647_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1));
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v_u_643_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_mkConst(v___x_647_, v___x_649_);
v___x_651_ = l_Lean_mkApp3(v___x_650_, v_00_u03c3s_644_, v_hyps_645_, v_target_646_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object* v_goal_652_){
_start:
{
lean_object* v_u_653_; lean_object* v_00_u03c3s_654_; lean_object* v_hyps_655_; lean_object* v_target_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_u_653_ = lean_ctor_get(v_goal_652_, 0);
lean_inc(v_u_653_);
v_00_u03c3s_654_ = lean_ctor_get(v_goal_652_, 1);
lean_inc_ref(v_00_u03c3s_654_);
v_hyps_655_ = lean_ctor_get(v_goal_652_, 2);
lean_inc_ref(v_hyps_655_);
v_target_656_ = lean_ctor_get(v_goal_652_, 3);
lean_inc_ref(v_target_656_);
lean_dec_ref(v_goal_652_);
v___x_657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2));
v___x_658_ = lean_box(0);
v___x_659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_659_, 0, v_u_653_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_mkConst(v___x_657_, v___x_659_);
v___x_661_ = l_Lean_mkApp3(v___x_660_, v_00_u03c3s_654_, v_hyps_655_, v_target_656_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(lean_object* v_msg_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_box(0);
v___x_664_ = lean_panic_fn_borrowed(v___x_663_, v_msg_662_);
return v___x_664_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2));
v___x_669_ = lean_unsigned_to_nat(8u);
v___x_670_ = lean_unsigned_to_nat(141u);
v___x_671_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1));
v___x_672_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0));
v___x_673_ = l_mkPanicMessageWithDecl(v___x_672_, v___x_671_, v___x_670_, v___x_669_, v___x_668_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(lean_object* v_name_674_, lean_object* v_e_675_, lean_object* v_p_676_){
_start:
{
lean_object* v___x_677_; 
lean_inc_ref(v_e_675_);
v___x_677_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_675_);
if (lean_obj_tag(v___x_677_) == 1)
{
lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_e_675_);
v_val_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_689_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_689_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_name_682_; uint8_t v___x_683_; 
v_name_682_ = lean_ctor_get(v_val_678_, 0);
v___x_683_ = lean_name_eq(v_name_682_, v_name_674_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_del_object(v___x_680_);
lean_dec(v_val_678_);
lean_dec(v_p_676_);
v___x_684_ = lean_box(0);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_p_676_);
lean_ctor_set(v___x_685_, 1, v_val_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_685_);
v___x_687_ = v___x_680_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_685_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v___x_690_; 
lean_dec(v___x_677_);
v___x_690_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_675_);
if (lean_obj_tag(v___x_690_) == 1)
{
lean_object* v_val_691_; lean_object* v_snd_692_; lean_object* v_snd_693_; lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref(v_e_675_);
v_val_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_691_);
lean_dec_ref(v___x_690_);
v_snd_692_ = lean_ctor_get(v_val_691_, 1);
lean_inc(v_snd_692_);
lean_dec(v_val_691_);
v_snd_693_ = lean_ctor_get(v_snd_692_, 1);
lean_inc(v_snd_693_);
lean_dec(v_snd_692_);
v_fst_694_ = lean_ctor_get(v_snd_693_, 0);
lean_inc(v_fst_694_);
v_snd_695_ = lean_ctor_get(v_snd_693_, 1);
lean_inc(v_snd_695_);
lean_dec(v_snd_693_);
v___x_696_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_p_676_);
v___x_697_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_674_, v_snd_695_, v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_p_676_);
lean_dec(v_p_676_);
v_e_675_ = v_fst_694_;
v_p_676_ = v___x_698_;
goto _start;
}
else
{
lean_dec(v_fst_694_);
lean_dec(v_p_676_);
return v___x_697_;
}
}
else
{
lean_object* v___x_700_; 
lean_dec(v___x_690_);
lean_dec(v_p_676_);
v___x_700_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_675_);
if (lean_obj_tag(v___x_700_) == 1)
{
lean_object* v___x_701_; 
lean_dec_ref(v___x_700_);
v___x_701_ = lean_box(0);
return v___x_701_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v___x_700_);
v___x_702_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3, &l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3);
v___x_703_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(v___x_702_);
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___boxed(lean_object* v_name_704_, lean_object* v_e_705_, lean_object* v_p_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_704_, v_e_705_, v_p_706_);
lean_dec(v_name_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(lean_object* v_goal_708_, lean_object* v_name_709_){
_start:
{
lean_object* v_hyps_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_hyps_710_ = lean_ctor_get(v_goal_708_, 2);
lean_inc_ref(v_hyps_710_);
lean_dec_ref(v_goal_708_);
v___x_711_ = l_Lean_SubExpr_Pos_root;
v___x_712_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_709_, v_hyps_710_, v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f___boxed(lean_object* v_goal_713_, lean_object* v_name_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_713_, v_name_714_);
lean_dec(v_name_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(lean_object* v_msg_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_ref_722_; lean_object* v___x_723_; lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_732_; 
v_ref_722_ = lean_ctor_get(v___y_719_, 5);
v___x_723_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_732_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_732_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_inc(v_ref_722_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_ref_722_);
lean_ctor_set(v___x_728_, 1, v_a_724_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
lean_ctor_set(v___x_726_, 0, v___x_728_);
v___x_730_ = v___x_726_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg___boxed(lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v_msg_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_747_, uint8_t v_suppressElabErrors_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_749_) == 1)
{
lean_object* v_pre_750_; 
v_pre_750_ = lean_ctor_get(v_x_749_, 0);
switch(lean_obj_tag(v_pre_750_))
{
case 1:
{
lean_object* v_pre_751_; 
v_pre_751_ = lean_ctor_get(v_pre_750_, 0);
switch(lean_obj_tag(v_pre_751_))
{
case 0:
{
lean_object* v_str_752_; lean_object* v_str_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_str_752_ = lean_ctor_get(v_x_749_, 1);
v_str_753_ = lean_ctor_get(v_pre_750_, 1);
v___x_754_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_755_ = lean_string_dec_eq(v_str_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0));
v___x_757_ = lean_string_dec_eq(v_str_753_, v___x_756_);
if (v___x_757_ == 0)
{
return v___y_747_;
}
else
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_759_ = lean_string_dec_eq(v_str_752_, v___x_758_);
if (v___x_759_ == 0)
{
return v___y_747_;
}
else
{
return v_suppressElabErrors_748_;
}
}
}
else
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_761_ = lean_string_dec_eq(v_str_752_, v___x_760_);
if (v___x_761_ == 0)
{
return v___y_747_;
}
else
{
return v_suppressElabErrors_748_;
}
}
}
case 1:
{
lean_object* v_pre_762_; 
v_pre_762_ = lean_ctor_get(v_pre_751_, 0);
if (lean_obj_tag(v_pre_762_) == 0)
{
lean_object* v_str_763_; lean_object* v_str_764_; lean_object* v_str_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_str_763_ = lean_ctor_get(v_x_749_, 1);
v_str_764_ = lean_ctor_get(v_pre_750_, 1);
v_str_765_ = lean_ctor_get(v_pre_751_, 1);
v___x_766_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_767_ = lean_string_dec_eq(v_str_765_, v___x_766_);
if (v___x_767_ == 0)
{
return v___y_747_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_769_ = lean_string_dec_eq(v_str_764_, v___x_768_);
if (v___x_769_ == 0)
{
return v___y_747_;
}
else
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_771_ = lean_string_dec_eq(v_str_763_, v___x_770_);
if (v___x_771_ == 0)
{
return v___y_747_;
}
else
{
return v_suppressElabErrors_748_;
}
}
}
}
else
{
return v___y_747_;
}
}
default: 
{
return v___y_747_;
}
}
}
case 0:
{
lean_object* v_str_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_str_772_ = lean_ctor_get(v_x_749_, 1);
v___x_773_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_774_ = lean_string_dec_eq(v_str_772_, v___x_773_);
if (v___x_774_ == 0)
{
return v___y_747_;
}
else
{
return v_suppressElabErrors_748_;
}
}
default: 
{
return v___y_747_;
}
}
}
else
{
return v___y_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_775_, lean_object* v_suppressElabErrors_776_, lean_object* v_x_777_){
_start:
{
uint8_t v___y_4448__boxed_778_; uint8_t v_suppressElabErrors_boxed_779_; uint8_t v_res_780_; lean_object* v_r_781_; 
v___y_4448__boxed_778_ = lean_unbox(v___y_775_);
v_suppressElabErrors_boxed_779_ = lean_unbox(v_suppressElabErrors_776_);
v_res_780_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(v___y_4448__boxed_778_, v_suppressElabErrors_boxed_779_, v_x_777_);
lean_dec(v_x_777_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_782_, lean_object* v_opt_783_){
_start:
{
lean_object* v_name_784_; lean_object* v_defValue_785_; lean_object* v_map_786_; lean_object* v___x_787_; 
v_name_784_ = lean_ctor_get(v_opt_783_, 0);
v_defValue_785_ = lean_ctor_get(v_opt_783_, 1);
v_map_786_ = lean_ctor_get(v_opts_782_, 0);
v___x_787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_786_, v_name_784_);
if (lean_obj_tag(v___x_787_) == 0)
{
uint8_t v___x_788_; 
v___x_788_ = lean_unbox(v_defValue_785_);
return v___x_788_;
}
else
{
lean_object* v_val_789_; 
v_val_789_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_val_789_);
lean_dec_ref(v___x_787_);
if (lean_obj_tag(v_val_789_) == 1)
{
uint8_t v_v_790_; 
v_v_790_ = lean_ctor_get_uint8(v_val_789_, 0);
lean_dec_ref(v_val_789_);
return v_v_790_;
}
else
{
uint8_t v___x_791_; 
lean_dec(v_val_789_);
v___x_791_ = lean_unbox(v_defValue_785_);
return v___x_791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_792_, lean_object* v_opt_793_){
_start:
{
uint8_t v_res_794_; lean_object* v_r_795_; 
v_res_794_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_opts_792_, v_opt_793_);
lean_dec_ref(v_opt_793_);
lean_dec_ref(v_opts_792_);
v_r_795_ = lean_box(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(lean_object* v_ref_797_, lean_object* v_msgData_798_, uint8_t v_severity_799_, uint8_t v_isSilent_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___y_807_; lean_object* v___y_808_; uint8_t v___y_809_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_843_; uint8_t v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; uint8_t v___y_847_; lean_object* v___y_848_; uint8_t v___y_849_; lean_object* v___y_850_; lean_object* v___y_868_; lean_object* v___y_869_; uint8_t v___y_870_; lean_object* v___y_871_; uint8_t v___y_872_; uint8_t v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_879_; uint8_t v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; uint8_t v___y_884_; uint8_t v___y_885_; uint8_t v___x_890_; lean_object* v___y_892_; uint8_t v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; uint8_t v___y_897_; uint8_t v___y_898_; uint8_t v___y_900_; uint8_t v___x_915_; 
v___x_890_ = 2;
v___x_915_ = l_Lean_instBEqMessageSeverity_beq(v_severity_799_, v___x_890_);
if (v___x_915_ == 0)
{
v___y_900_ = v___x_915_;
goto v___jp_899_;
}
else
{
uint8_t v___x_916_; 
lean_inc_ref(v_msgData_798_);
v___x_916_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_798_);
v___y_900_ = v___x_916_;
goto v___jp_899_;
}
v___jp_806_:
{
lean_object* v___x_816_; lean_object* v_currNamespace_817_; lean_object* v_openDecls_818_; lean_object* v_env_819_; lean_object* v_nextMacroScope_820_; lean_object* v_ngen_821_; lean_object* v_auxDeclNGen_822_; lean_object* v_traceState_823_; lean_object* v_cache_824_; lean_object* v_messages_825_; lean_object* v_infoState_826_; lean_object* v_snapshotTasks_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_841_; 
v___x_816_ = lean_st_ref_take(v___y_815_);
v_currNamespace_817_ = lean_ctor_get(v___y_814_, 6);
v_openDecls_818_ = lean_ctor_get(v___y_814_, 7);
v_env_819_ = lean_ctor_get(v___x_816_, 0);
v_nextMacroScope_820_ = lean_ctor_get(v___x_816_, 1);
v_ngen_821_ = lean_ctor_get(v___x_816_, 2);
v_auxDeclNGen_822_ = lean_ctor_get(v___x_816_, 3);
v_traceState_823_ = lean_ctor_get(v___x_816_, 4);
v_cache_824_ = lean_ctor_get(v___x_816_, 5);
v_messages_825_ = lean_ctor_get(v___x_816_, 6);
v_infoState_826_ = lean_ctor_get(v___x_816_, 7);
v_snapshotTasks_827_ = lean_ctor_get(v___x_816_, 8);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_841_ == 0)
{
v___x_829_ = v___x_816_;
v_isShared_830_ = v_isSharedCheck_841_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_snapshotTasks_827_);
lean_inc(v_infoState_826_);
lean_inc(v_messages_825_);
lean_inc(v_cache_824_);
lean_inc(v_traceState_823_);
lean_inc(v_auxDeclNGen_822_);
lean_inc(v_ngen_821_);
lean_inc(v_nextMacroScope_820_);
lean_inc(v_env_819_);
lean_dec(v___x_816_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_841_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_openDecls_818_);
lean_inc(v_currNamespace_817_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_currNamespace_817_);
lean_ctor_set(v___x_831_, 1, v_openDecls_818_);
v___x_832_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___y_813_);
lean_inc_ref(v___y_808_);
lean_inc_ref(v___y_812_);
v___x_833_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_833_, 0, v___y_812_);
lean_ctor_set(v___x_833_, 1, v___y_807_);
lean_ctor_set(v___x_833_, 2, v___y_810_);
lean_ctor_set(v___x_833_, 3, v___y_808_);
lean_ctor_set(v___x_833_, 4, v___x_832_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*5, v___y_811_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*5 + 1, v___y_809_);
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*5 + 2, v_isSilent_800_);
v___x_834_ = l_Lean_MessageLog_add(v___x_833_, v_messages_825_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 6, v___x_834_);
v___x_836_ = v___x_829_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_env_819_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_nextMacroScope_820_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_ngen_821_);
lean_ctor_set(v_reuseFailAlloc_840_, 3, v_auxDeclNGen_822_);
lean_ctor_set(v_reuseFailAlloc_840_, 4, v_traceState_823_);
lean_ctor_set(v_reuseFailAlloc_840_, 5, v_cache_824_);
lean_ctor_set(v_reuseFailAlloc_840_, 6, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_840_, 7, v_infoState_826_);
lean_ctor_set(v_reuseFailAlloc_840_, 8, v_snapshotTasks_827_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_st_ref_set(v___y_815_, v___x_836_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
}
v___jp_842_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_866_; 
v___x_851_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_798_);
v___x_852_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v___x_851_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_866_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_866_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_inc_ref_n(v___y_846_, 2);
v___x_857_ = l_Lean_FileMap_toPosition(v___y_846_, v___y_845_);
lean_dec(v___y_845_);
v___x_858_ = l_Lean_FileMap_toPosition(v___y_846_, v___y_850_);
lean_dec(v___y_850_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
v___x_860_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0));
if (v___y_844_ == 0)
{
lean_del_object(v___x_855_);
lean_dec_ref(v___y_843_);
v___y_807_ = v___x_857_;
v___y_808_ = v___x_860_;
v___y_809_ = v___y_847_;
v___y_810_ = v___x_859_;
v___y_811_ = v___y_849_;
v___y_812_ = v___y_848_;
v___y_813_ = v_a_853_;
v___y_814_ = v___y_803_;
v___y_815_ = v___y_804_;
goto v___jp_806_;
}
else
{
uint8_t v___x_861_; 
lean_inc(v_a_853_);
v___x_861_ = l_Lean_MessageData_hasTag(v___y_843_, v_a_853_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec_ref(v___x_859_);
lean_dec_ref(v___x_857_);
lean_dec(v_a_853_);
v___x_862_ = lean_box(0);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_862_);
v___x_864_ = v___x_855_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_del_object(v___x_855_);
v___y_807_ = v___x_857_;
v___y_808_ = v___x_860_;
v___y_809_ = v___y_847_;
v___y_810_ = v___x_859_;
v___y_811_ = v___y_849_;
v___y_812_ = v___y_848_;
v___y_813_ = v_a_853_;
v___y_814_ = v___y_803_;
v___y_815_ = v___y_804_;
goto v___jp_806_;
}
}
}
}
v___jp_867_:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Syntax_getTailPos_x3f(v___y_869_, v___y_873_);
lean_dec(v___y_869_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_inc(v___y_875_);
v___y_843_ = v___y_868_;
v___y_844_ = v___y_870_;
v___y_845_ = v___y_875_;
v___y_846_ = v___y_871_;
v___y_847_ = v___y_872_;
v___y_848_ = v___y_874_;
v___y_849_ = v___y_873_;
v___y_850_ = v___y_875_;
goto v___jp_842_;
}
else
{
lean_object* v_val_877_; 
v_val_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_val_877_);
lean_dec_ref(v___x_876_);
v___y_843_ = v___y_868_;
v___y_844_ = v___y_870_;
v___y_845_ = v___y_875_;
v___y_846_ = v___y_871_;
v___y_847_ = v___y_872_;
v___y_848_ = v___y_874_;
v___y_849_ = v___y_873_;
v___y_850_ = v_val_877_;
goto v___jp_842_;
}
}
v___jp_878_:
{
lean_object* v_ref_886_; lean_object* v___x_887_; 
v_ref_886_ = l_Lean_replaceRef(v_ref_797_, v___y_881_);
v___x_887_ = l_Lean_Syntax_getPos_x3f(v_ref_886_, v___y_884_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = lean_unsigned_to_nat(0u);
v___y_868_ = v___y_879_;
v___y_869_ = v_ref_886_;
v___y_870_ = v___y_880_;
v___y_871_ = v___y_882_;
v___y_872_ = v___y_885_;
v___y_873_ = v___y_884_;
v___y_874_ = v___y_883_;
v___y_875_ = v___x_888_;
goto v___jp_867_;
}
else
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_889_);
lean_dec_ref(v___x_887_);
v___y_868_ = v___y_879_;
v___y_869_ = v_ref_886_;
v___y_870_ = v___y_880_;
v___y_871_ = v___y_882_;
v___y_872_ = v___y_885_;
v___y_873_ = v___y_884_;
v___y_874_ = v___y_883_;
v___y_875_ = v_val_889_;
goto v___jp_867_;
}
}
v___jp_891_:
{
if (v___y_898_ == 0)
{
v___y_879_ = v___y_894_;
v___y_880_ = v___y_893_;
v___y_881_ = v___y_892_;
v___y_882_ = v___y_895_;
v___y_883_ = v___y_896_;
v___y_884_ = v___y_897_;
v___y_885_ = v_severity_799_;
goto v___jp_878_;
}
else
{
v___y_879_ = v___y_894_;
v___y_880_ = v___y_893_;
v___y_881_ = v___y_892_;
v___y_882_ = v___y_895_;
v___y_883_ = v___y_896_;
v___y_884_ = v___y_897_;
v___y_885_ = v___x_890_;
goto v___jp_878_;
}
}
v___jp_899_:
{
if (v___y_900_ == 0)
{
lean_object* v_fileName_901_; lean_object* v_fileMap_902_; lean_object* v_options_903_; lean_object* v_ref_904_; uint8_t v_suppressElabErrors_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; uint8_t v___x_909_; uint8_t v___x_910_; 
v_fileName_901_ = lean_ctor_get(v___y_803_, 0);
v_fileMap_902_ = lean_ctor_get(v___y_803_, 1);
v_options_903_ = lean_ctor_get(v___y_803_, 2);
v_ref_904_ = lean_ctor_get(v___y_803_, 5);
v_suppressElabErrors_905_ = lean_ctor_get_uint8(v___y_803_, sizeof(void*)*14 + 1);
v___x_906_ = lean_box(v___y_900_);
v___x_907_ = lean_box(v_suppressElabErrors_905_);
v___f_908_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_908_, 0, v___x_906_);
lean_closure_set(v___f_908_, 1, v___x_907_);
v___x_909_ = 1;
v___x_910_ = l_Lean_instBEqMessageSeverity_beq(v_severity_799_, v___x_909_);
if (v___x_910_ == 0)
{
v___y_892_ = v_ref_904_;
v___y_893_ = v_suppressElabErrors_905_;
v___y_894_ = v___f_908_;
v___y_895_ = v_fileMap_902_;
v___y_896_ = v_fileName_901_;
v___y_897_ = v___y_900_;
v___y_898_ = v___x_910_;
goto v___jp_891_;
}
else
{
lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_911_ = l_Lean_warningAsError;
v___x_912_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_options_903_, v___x_911_);
v___y_892_ = v_ref_904_;
v___y_893_ = v_suppressElabErrors_905_;
v___y_894_ = v___f_908_;
v___y_895_ = v_fileMap_902_;
v___y_896_ = v_fileName_901_;
v___y_897_ = v___y_900_;
v___y_898_ = v___x_912_;
goto v___jp_891_;
}
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v_msgData_798_);
v___x_913_ = lean_box(0);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_917_, lean_object* v_msgData_918_, lean_object* v_severity_919_, lean_object* v_isSilent_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
uint8_t v_severity_boxed_926_; uint8_t v_isSilent_boxed_927_; lean_object* v_res_928_; 
v_severity_boxed_926_ = lean_unbox(v_severity_919_);
v_isSilent_boxed_927_ = lean_unbox(v_isSilent_920_);
v_res_928_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_917_, v_msgData_918_, v_severity_boxed_926_, v_isSilent_boxed_927_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v_ref_917_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(lean_object* v_msgData_929_, uint8_t v_severity_930_, uint8_t v_isSilent_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_ref_937_; lean_object* v___x_938_; 
v_ref_937_ = lean_ctor_get(v___y_934_, 5);
v___x_938_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_937_, v_msgData_929_, v_severity_930_, v_isSilent_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0___boxed(lean_object* v_msgData_939_, lean_object* v_severity_940_, lean_object* v_isSilent_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v_severity_boxed_947_; uint8_t v_isSilent_boxed_948_; lean_object* v_res_949_; 
v_severity_boxed_947_ = lean_unbox(v_severity_940_);
v_isSilent_boxed_948_ = lean_unbox(v_isSilent_941_);
v_res_949_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_939_, v_severity_boxed_947_, v_isSilent_boxed_948_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(lean_object* v_msgData_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
uint8_t v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = 1;
v___x_957_ = 0;
v___x_958_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_950_, v___x_956_, v___x_957_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0___boxed(lean_object* v_msgData_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v_msgData_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(lean_object* v_expr_981_, lean_object* v_expectedType_982_, uint8_t v_suppressWarning_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___x_1004_; 
lean_inc_ref(v_expr_981_);
v___x_1004_ = l_Lean_Meta_check(v_expr_981_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v___x_1005_; 
lean_dec_ref(v___x_1004_);
lean_inc_ref(v_expectedType_982_);
v___x_1005_ = l_Lean_Meta_check(v_expectedType_982_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v___x_1006_; 
lean_dec_ref(v___x_1005_);
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
lean_inc(v_a_985_);
lean_inc_ref(v_a_984_);
lean_inc_ref(v_expr_981_);
v___x_1006_ = lean_infer_type(v_expr_981_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc_n(v_a_1007_, 2);
lean_dec_ref(v___x_1006_);
lean_inc_ref(v_expectedType_982_);
v___x_1008_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1007_, v_expectedType_982_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; uint8_t v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = lean_unbox(v_a_1009_);
lean_dec(v_a_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1011_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5);
v___x_1012_ = l_Lean_indentExpr(v_expr_981_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_indentExpr(v_a_1007_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_indentExpr(v_expectedType_982_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1021_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_1022_;
}
else
{
lean_dec(v_a_1007_);
v___y_990_ = v_a_984_;
v___y_991_ = v_a_985_;
v___y_992_ = v_a_986_;
v___y_993_ = v_a_987_;
goto v___jp_989_;
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec(v_a_1007_);
lean_dec_ref(v_expectedType_982_);
lean_dec_ref(v_expr_981_);
v_a_1023_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1008_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1008_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_expectedType_982_);
lean_dec_ref(v_expr_981_);
v_a_1031_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1006_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1006_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_982_);
lean_dec_ref(v_expr_981_);
return v___x_1005_;
}
}
else
{
lean_dec_ref(v_expectedType_982_);
lean_dec_ref(v_expr_981_);
return v___x_1004_;
}
v___jp_989_:
{
if (v_suppressWarning_983_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_994_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1);
v___x_995_ = l_Lean_MessageData_ofExpr(v_expr_981_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Lean_MessageData_ofExpr(v_expectedType_982_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v___x_1000_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v_expectedType_982_);
lean_dec_ref(v_expr_981_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___boxed(lean_object* v_expr_1039_, lean_object* v_expectedType_1040_, lean_object* v_suppressWarning_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
uint8_t v_suppressWarning_boxed_1047_; lean_object* v_res_1048_; 
v_suppressWarning_boxed_1047_ = lean_unbox(v_suppressWarning_1041_);
v_res_1048_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(v_expr_1039_, v_expectedType_1040_, v_suppressWarning_boxed_1047_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(lean_object* v_00_u03b1_1049_, lean_object* v_msg_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v_msg_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_msg_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(v_00_u03b1_1057_, v_msg_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(lean_object* v_goal_1065_, lean_object* v_prf_1066_, uint8_t v_suppressWarning_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1065_);
v___x_1074_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(v_prf_1066_, v___x_1073_, v_suppressWarning_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof___boxed(lean_object* v_goal_1075_, lean_object* v_prf_1076_, lean_object* v_suppressWarning_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
uint8_t v_suppressWarning_boxed_1083_; lean_object* v_res_1084_; 
v_suppressWarning_boxed_1083_ = lean_unbox(v_suppressWarning_1077_);
v_res_1084_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(v_goal_1075_, v_prf_1076_, v_suppressWarning_boxed_1083_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object* v_x_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2));
lean_inc(v_x_1096_);
v___x_1101_ = l_Lean_Syntax_isOfKind(v_x_1096_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4));
v___x_1103_ = l_Lean_Core_mkFreshUserName(v___x_1102_, v_a_1097_, v_a_1098_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1112_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1112_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_a_1104_);
lean_ctor_set(v___x_1108_, 1, v_x_1096_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1108_);
v___x_1110_ = v___x_1106_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec(v_x_1096_);
v_a_1113_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1103_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1103_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
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
else
{
lean_object* v___x_1121_; lean_object* v_name_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v_name_1122_ = l_Lean_Syntax_getArg(v_x_1096_, v___x_1121_);
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6));
lean_inc(v_name_1122_);
v___x_1124_ = l_Lean_Syntax_isOfKind(v_name_1122_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_name_1122_);
v___x_1125_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4));
v___x_1126_ = l_Lean_Core_mkFreshUserName(v___x_1125_, v_a_1097_, v_a_1098_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1135_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1135_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1135_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_a_1127_);
lean_ctor_set(v___x_1131_, 1, v_x_1096_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1131_);
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_x_1096_);
v_a_1136_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1126_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1126_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
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
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
lean_dec(v_x_1096_);
v___x_1144_ = l_Lean_TSyntax_getId(v_name_1122_);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_name_1122_);
v___x_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___boxed(lean_object* v_x_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_x_1147_, v_a_1148_, v_a_1149_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(lean_object* v_as_1152_, size_t v_i_1153_, size_t v_stop_1154_, lean_object* v_b_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_eq(v_i_1153_, v_stop_1154_);
if (v___x_1156_ == 0)
{
size_t v___x_1157_; size_t v___x_1158_; lean_object* v___x_1159_; lean_object* v_snd_1160_; lean_object* v_fst_1161_; lean_object* v_fst_1162_; lean_object* v_snd_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; 
v___x_1157_ = ((size_t)1ULL);
v___x_1158_ = lean_usize_sub(v_i_1153_, v___x_1157_);
v___x_1159_ = lean_array_uget_borrowed(v_as_1152_, v___x_1158_);
v_snd_1160_ = lean_ctor_get(v___x_1159_, 1);
v_fst_1161_ = lean_ctor_get(v___x_1159_, 0);
v_fst_1162_ = lean_ctor_get(v_snd_1160_, 0);
v_snd_1163_ = lean_ctor_get(v_snd_1160_, 1);
v___x_1164_ = lean_unbox(v_snd_1163_);
lean_inc(v_fst_1162_);
lean_inc(v_fst_1161_);
v___x_1165_ = l_Lean_Expr_lam___override(v_fst_1161_, v_fst_1162_, v_b_1155_, v___x_1164_);
v_i_1153_ = v___x_1158_;
v_b_1155_ = v___x_1165_;
goto _start;
}
else
{
return v_b_1155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0___boxed(lean_object* v_as_1167_, lean_object* v_i_1168_, lean_object* v_stop_1169_, lean_object* v_b_1170_){
_start:
{
size_t v_i_boxed_1171_; size_t v_stop_boxed_1172_; lean_object* v_res_1173_; 
v_i_boxed_1171_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v_stop_boxed_1172_ = lean_unbox_usize(v_stop_1169_);
lean_dec(v_stop_1169_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_as_1167_, v_i_boxed_1171_, v_stop_boxed_1172_, v_b_1170_);
lean_dec_ref(v_as_1167_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(lean_object* v_revLams_1174_, lean_object* v_revAppArgs_1175_, lean_object* v_body_1176_){
_start:
{
uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1177_ = 0;
v___x_1178_ = l_Lean_Expr_betaRev(v_body_1176_, v_revAppArgs_1175_, v___x_1177_, v___x_1177_);
v___x_1179_ = lean_array_get_size(v_revLams_1174_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = lean_nat_dec_lt(v___x_1180_, v___x_1179_);
if (v___x_1181_ == 0)
{
return v___x_1178_;
}
else
{
size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_usize_of_nat(v___x_1179_);
v___x_1183_ = ((size_t)0ULL);
v___x_1184_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_revLams_1174_, v___x_1182_, v___x_1183_, v___x_1178_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap___boxed(lean_object* v_revLams_1185_, lean_object* v_revAppArgs_1186_, lean_object* v_body_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1185_, v_revAppArgs_1186_, v_body_1187_);
lean_dec_ref(v_revAppArgs_1186_);
lean_dec_ref(v_revLams_1185_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(lean_object* v_00_u03c3s_1189_, lean_object* v_revLams_1190_, lean_object* v_revAppArgs_1191_, lean_object* v_e_1192_){
_start:
{
lean_object* v___x_1193_; 
lean_inc_ref(v_e_1192_);
v___x_1193_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_1192_);
if (lean_obj_tag(v___x_1193_) == 1)
{
lean_object* v_val_1194_; lean_object* v_fst_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_revAppArgs_1191_);
lean_dec_ref(v_revLams_1190_);
v_val_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_val_1194_);
lean_dec_ref(v___x_1193_);
v_fst_1195_ = lean_ctor_get(v_val_1194_, 0);
lean_inc(v_fst_1195_);
lean_dec(v_val_1194_);
v___x_1196_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_fst_1195_, v_00_u03c3s_1189_);
return v___x_1196_;
}
else
{
lean_object* v___x_1197_; 
lean_dec(v___x_1193_);
lean_inc_ref(v_e_1192_);
v___x_1197_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_1192_);
if (lean_obj_tag(v___x_1197_) == 1)
{
lean_object* v_val_1198_; lean_object* v_name_1199_; lean_object* v_uniq_1200_; lean_object* v_p_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_00_u03c3s_1189_);
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref(v___x_1197_);
v_name_1199_ = lean_ctor_get(v_val_1198_, 0);
v_uniq_1200_ = lean_ctor_get(v_val_1198_, 1);
v_p_1201_ = lean_ctor_get(v_val_1198_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_val_1198_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1203_ = v_val_1198_;
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_p_1201_);
lean_inc(v_uniq_1200_);
lean_inc(v_name_1199_);
lean_dec(v_val_1198_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1190_, v_revAppArgs_1191_, v_p_1201_);
lean_dec_ref(v_revAppArgs_1191_);
lean_dec_ref(v_revLams_1190_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 2, v___x_1205_);
v___x_1207_ = v___x_1203_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_name_1199_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_uniq_1200_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1207_);
return v___x_1208_;
}
}
}
else
{
lean_object* v___x_1211_; 
lean_dec(v___x_1197_);
v___x_1211_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_1192_);
if (lean_obj_tag(v___x_1211_) == 1)
{
lean_object* v_val_1212_; lean_object* v_snd_1213_; lean_object* v_snd_1214_; lean_object* v_fst_1215_; lean_object* v_fst_1216_; lean_object* v_snd_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v_e_1192_);
v_val_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1212_);
lean_dec_ref(v___x_1211_);
v_snd_1213_ = lean_ctor_get(v_val_1212_, 1);
v_snd_1214_ = lean_ctor_get(v_snd_1213_, 1);
lean_inc(v_snd_1214_);
v_fst_1215_ = lean_ctor_get(v_val_1212_, 0);
lean_inc(v_fst_1215_);
lean_dec(v_val_1212_);
v_fst_1216_ = lean_ctor_get(v_snd_1214_, 0);
lean_inc(v_fst_1216_);
v_snd_1217_ = lean_ctor_get(v_snd_1214_, 1);
lean_inc(v_snd_1217_);
lean_dec(v_snd_1214_);
lean_inc_ref(v_revAppArgs_1191_);
lean_inc_ref(v_revLams_1190_);
lean_inc_ref_n(v_00_u03c3s_1189_, 2);
v___x_1218_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1189_, v_revLams_1190_, v_revAppArgs_1191_, v_fst_1216_);
v___x_1219_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1189_, v_revLams_1190_, v_revAppArgs_1191_, v_snd_1217_);
v___x_1220_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_1215_, v_00_u03c3s_1189_, v___x_1218_, v___x_1219_);
return v___x_1220_;
}
else
{
lean_dec(v___x_1211_);
if (lean_obj_tag(v_e_1192_) == 6)
{
lean_object* v_binderName_1221_; lean_object* v_binderType_1222_; lean_object* v_body_1223_; uint8_t v_binderInfo_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
v_binderName_1221_ = lean_ctor_get(v_e_1192_, 0);
lean_inc(v_binderName_1221_);
v_binderType_1222_ = lean_ctor_get(v_e_1192_, 1);
lean_inc_ref(v_binderType_1222_);
v_body_1223_ = lean_ctor_get(v_e_1192_, 2);
lean_inc_ref(v_body_1223_);
v_binderInfo_1224_ = lean_ctor_get_uint8(v_e_1192_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_1192_);
v___x_1225_ = lean_array_get_size(v_revAppArgs_1191_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_sub(v___x_1225_, v___x_1226_);
v___x_1228_ = lean_nat_dec_lt(v___x_1227_, v___x_1225_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v___x_1227_);
v___x_1229_ = lean_box(v_binderInfo_1224_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_binderType_1222_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_binderName_1221_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_array_push(v_revLams_1190_, v___x_1231_);
v_revLams_1190_ = v___x_1232_;
v_e_1192_ = v_body_1223_;
goto _start;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec_ref(v_binderType_1222_);
lean_dec(v_binderName_1221_);
v___x_1234_ = lean_array_fget(v_revAppArgs_1191_, v___x_1227_);
lean_dec(v___x_1227_);
v___x_1235_ = lean_array_pop(v_revAppArgs_1191_);
v___x_1236_ = lean_expr_instantiate1(v_body_1223_, v___x_1234_);
lean_dec(v___x_1234_);
lean_dec_ref(v_body_1223_);
v_revAppArgs_1191_ = v___x_1235_;
v_e_1192_ = v___x_1236_;
goto _start;
}
}
else
{
if (lean_obj_tag(v_e_1192_) == 5)
{
lean_object* v_fn_1238_; lean_object* v_arg_1239_; lean_object* v___x_1240_; 
v_fn_1238_ = lean_ctor_get(v_e_1192_, 0);
lean_inc_ref(v_fn_1238_);
v_arg_1239_ = lean_ctor_get(v_e_1192_, 1);
lean_inc_ref(v_arg_1239_);
lean_dec_ref(v_e_1192_);
v___x_1240_ = lean_array_push(v_revAppArgs_1191_, v_arg_1239_);
v_revAppArgs_1191_ = v___x_1240_;
v_e_1192_ = v_fn_1238_;
goto _start;
}
else
{
lean_object* v___x_1242_; 
lean_dec_ref(v_00_u03c3s_1189_);
v___x_1242_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1190_, v_revAppArgs_1191_, v_e_1192_);
lean_dec_ref(v_revAppArgs_1191_);
lean_dec_ref(v_revLams_1190_);
return v___x_1242_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(lean_object* v_00_u03c3s_1245_, lean_object* v_hyps_1246_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0));
v___x_1248_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1245_, v___x_1247_, v___x_1247_, v_hyps_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(lean_object* v_00_u03c3s_x27_1249_, lean_object* v_e_1250_, lean_object* v_args_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_mkAppN(v_e_1250_, v_args_1251_);
v___x_1253_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v_00_u03c3s_x27_1249_, v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames___boxed(lean_object* v_00_u03c3s_x27_1254_, lean_object* v_e_1255_, lean_object* v_args_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(v_00_u03c3s_x27_1254_, v_e_1255_, v_args_1256_);
lean_dec_ref(v_args_1256_);
return v_res_1257_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(lean_object* v_upperBound_1261_, lean_object* v_a_1262_, lean_object* v_b_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_a_1270_; uint8_t v___x_1274_; 
v___x_1274_ = lean_nat_dec_lt(v_a_1262_, v_upperBound_1261_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v_a_1262_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_b_1263_);
return v___x_1275_;
}
else
{
lean_object* v___x_1276_; 
lean_inc_ref(v_b_1263_);
v___x_1276_ = l_Lean_Meta_whnfR(v_b_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref(v___x_1276_);
v___x_1278_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1));
v___x_1279_ = lean_unsigned_to_nat(3u);
v___x_1280_ = l_Lean_Expr_isAppOfArity(v_a_1277_, v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec(v_a_1277_);
v___x_1281_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1);
lean_inc_ref(v_b_1263_);
v___x_1282_ = l_Lean_MessageData_ofExpr(v_b_1263_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1283_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec_ref(v___x_1284_);
v_a_1270_ = v_b_1263_;
goto v___jp_1269_;
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_b_1263_);
lean_dec(v_a_1262_);
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v___x_1293_; 
lean_dec_ref(v_b_1263_);
v___x_1293_ = l_Lean_Expr_appArg_x21(v_a_1277_);
lean_dec(v_a_1277_);
v_a_1270_ = v___x_1293_;
goto v___jp_1269_;
}
}
else
{
lean_dec_ref(v_b_1263_);
lean_dec(v_a_1262_);
return v___x_1276_;
}
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_unsigned_to_nat(1u);
v___x_1272_ = lean_nat_add(v_a_1262_, v___x_1271_);
lean_dec(v_a_1262_);
v_a_1262_ = v___x_1272_;
v_b_1263_ = v_a_1270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___boxed(lean_object* v_upperBound_1294_, lean_object* v_a_1295_, lean_object* v_b_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_1294_, v_a_1295_, v_b_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v_upperBound_1294_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(lean_object* v_00_u03c3s_1303_, lean_object* v_n_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_n_1304_, v___x_1310_, v_00_u03c3s_1303_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList___boxed(lean_object* v_00_u03c3s_1312_, lean_object* v_n_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(v_00_u03c3s_1312_, v_n_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec(v_a_1317_);
lean_dec_ref(v_a_1316_);
lean_dec(v_a_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v_n_1313_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(lean_object* v_upperBound_1320_, lean_object* v_inst_1321_, lean_object* v_R_1322_, lean_object* v_a_1323_, lean_object* v_b_1324_, lean_object* v_c_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_1320_, v_a_1323_, v_b_1324_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___boxed(lean_object* v_upperBound_1332_, lean_object* v_inst_1333_, lean_object* v_R_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_, lean_object* v_c_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(v_upperBound_1332_, v_inst_1333_, v_R_1334_, v_a_1335_, v_b_1336_, v_c_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v_upperBound_1332_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(lean_object* v_H_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_fst_1347_ = lean_ctor_get(v_a_1345_, 0);
v_snd_1348_ = lean_ctor_get(v_a_1345_, 1);
v___x_1349_ = lean_array_get_size(v_snd_1348_);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_nat_dec_eq(v___x_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_inc_ref(v_H_1344_);
v___x_1352_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_H_1344_);
if (lean_obj_tag(v___x_1352_) == 1)
{
lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1361_);
v___x_1354_ = v___x_1352_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_dec(v___x_1352_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_H_1344_);
lean_ctor_set(v___x_1356_, 1, v_a_1345_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v___x_1362_; 
lean_dec(v___x_1352_);
lean_inc_ref(v_H_1344_);
v___x_1362_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_H_1344_);
if (lean_obj_tag(v___x_1362_) == 1)
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1411_; 
lean_inc(v_snd_1348_);
lean_inc(v_fst_1347_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_a_1345_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; lean_object* v_unused_1413_; 
v_unused_1412_ = lean_ctor_get(v_a_1345_, 1);
lean_dec(v_unused_1412_);
v_unused_1413_ = lean_ctor_get(v_a_1345_, 0);
lean_dec(v_unused_1413_);
v___x_1364_ = v_a_1345_;
v_isShared_1365_ = v_isSharedCheck_1411_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v_a_1345_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1411_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_val_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1410_; 
v_val_1366_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1368_ = v___x_1362_;
v_isShared_1369_ = v_isSharedCheck_1410_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_val_1366_);
lean_dec(v___x_1362_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1410_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_name_1370_; lean_object* v_uniq_1371_; lean_object* v_p_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1409_; 
v_name_1370_ = lean_ctor_get(v_val_1366_, 0);
v_uniq_1371_ = lean_ctor_get(v_val_1366_, 1);
v_p_1372_ = lean_ctor_get(v_val_1366_, 2);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_val_1366_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1374_ = v_val_1366_;
v_isShared_1375_ = v_isSharedCheck_1409_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_p_1372_);
lean_inc(v_uniq_1371_);
lean_inc(v_name_1370_);
lean_dec(v_val_1366_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1409_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v_idents_1377_; uint8_t v___x_1407_; 
v___x_1407_ = l_Lean_Name_hasMacroScopes(v_name_1370_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_NameSet_contains(v_fst_1347_, v_name_1370_);
if (v___x_1408_ == 0)
{
lean_del_object(v___x_1374_);
lean_dec_ref(v_p_1372_);
lean_dec(v_uniq_1371_);
v_idents_1377_ = v_snd_1348_;
goto v___jp_1376_;
}
else
{
goto v___jp_1386_;
}
}
else
{
goto v___jp_1386_;
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1378_ = l_Lean_NameSet_insert(v_fst_1347_, v_name_1370_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 1, v_idents_1377_);
lean_ctor_set(v___x_1364_, 0, v___x_1378_);
v___x_1380_ = v___x_1364_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_idents_1377_);
v___x_1380_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_H_1344_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set_tag(v___x_1368_, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1381_);
v___x_1383_ = v___x_1368_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
v___jp_1386_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2));
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_nat_sub(v___x_1349_, v___x_1389_);
v___x_1391_ = lean_array_get_borrowed(v___x_1388_, v_snd_1348_, v___x_1390_);
lean_dec(v___x_1390_);
lean_inc(v___x_1391_);
v___x_1392_ = l_Lean_Syntax_isOfKind(v___x_1391_, v___x_1387_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_del_object(v___x_1374_);
lean_dec_ref(v_p_1372_);
lean_dec(v_uniq_1371_);
v___x_1393_ = lean_array_pop(v_snd_1348_);
v_idents_1377_ = v___x_1393_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = l_Lean_Syntax_getArg(v___x_1391_, v___x_1350_);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6));
lean_inc(v___x_1394_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v___x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v___x_1394_);
lean_del_object(v___x_1374_);
lean_dec_ref(v_p_1372_);
lean_dec(v_uniq_1371_);
v___x_1397_ = lean_array_pop(v_snd_1348_);
v_idents_1377_ = v___x_1397_;
goto v___jp_1376_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_dec(v_name_1370_);
lean_del_object(v___x_1368_);
lean_del_object(v___x_1364_);
lean_dec_ref(v_H_1344_);
v___x_1398_ = l_Lean_TSyntax_getId(v___x_1394_);
lean_dec(v___x_1394_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1398_);
v___x_1400_ = v___x_1374_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_uniq_1371_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_p_1372_);
v___x_1400_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1401_ = lean_array_pop(v_snd_1348_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_fst_1347_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1400_);
v___x_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
lean_ctor_set(v___x_1404_, 1, v___x_1402_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
return v___x_1405_;
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
lean_object* v___x_1414_; 
lean_dec(v___x_1362_);
v___x_1414_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_H_1344_);
if (lean_obj_tag(v___x_1414_) == 1)
{
lean_object* v_val_1415_; lean_object* v_snd_1416_; lean_object* v_snd_1417_; lean_object* v_fst_1418_; lean_object* v_fst_1419_; lean_object* v_fst_1420_; lean_object* v_snd_1421_; lean_object* v___x_1422_; 
lean_dec_ref(v_H_1344_);
v_val_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_val_1415_);
lean_dec_ref(v___x_1414_);
v_snd_1416_ = lean_ctor_get(v_val_1415_, 1);
lean_inc(v_snd_1416_);
v_snd_1417_ = lean_ctor_get(v_snd_1416_, 1);
lean_inc(v_snd_1417_);
v_fst_1418_ = lean_ctor_get(v_val_1415_, 0);
lean_inc(v_fst_1418_);
lean_dec(v_val_1415_);
v_fst_1419_ = lean_ctor_get(v_snd_1416_, 0);
lean_inc(v_fst_1419_);
lean_dec(v_snd_1416_);
v_fst_1420_ = lean_ctor_get(v_snd_1417_, 0);
lean_inc(v_fst_1420_);
v_snd_1421_ = lean_ctor_get(v_snd_1417_, 1);
lean_inc(v_snd_1421_);
lean_dec(v_snd_1417_);
v___x_1422_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_snd_1421_, v_a_1345_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_fst_1424_; lean_object* v_snd_1425_; lean_object* v___x_1426_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
v_fst_1424_ = lean_ctor_get(v_a_1423_, 0);
lean_inc(v_fst_1424_);
v_snd_1425_ = lean_ctor_get(v_a_1423_, 1);
lean_inc(v_snd_1425_);
lean_dec(v_a_1423_);
v___x_1426_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_fst_1420_, v_snd_1425_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1444_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1443_; 
v_fst_1431_ = lean_ctor_get(v_a_1427_, 0);
v_snd_1432_ = lean_ctor_get(v_a_1427_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_a_1427_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1434_ = v_a_1427_;
v_isShared_1435_ = v_isSharedCheck_1443_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v_a_1427_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1443_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_1418_, v_fst_1419_, v_fst_1431_, v_fst_1424_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1432_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1438_);
v___x_1440_ = v___x_1429_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
else
{
lean_dec(v_fst_1424_);
lean_dec(v_fst_1419_);
lean_dec(v_fst_1418_);
return v___x_1426_;
}
}
else
{
lean_dec(v_fst_1420_);
lean_dec(v_fst_1419_);
lean_dec(v_fst_1418_);
return v___x_1422_;
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v___x_1414_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_H_1344_);
lean_ctor_set(v___x_1445_, 1, v_a_1345_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
}
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v_H_1344_);
lean_ctor_set(v___x_1447_, 1, v_a_1345_);
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg___boxed(lean_object* v_H_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_1449_, v_a_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(lean_object* v_H_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_1453_, v_a_1454_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___boxed(lean_object* v_H_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(v_H_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v___x_1471_; 
v___x_1471_ = l_List_reverse___redArg(v_a_1470_);
return v___x_1471_;
}
else
{
lean_object* v_head_1472_; lean_object* v_tail_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
v_head_1472_ = lean_ctor_get(v_a_1469_, 0);
v_tail_1473_ = lean_ctor_get(v_a_1469_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1475_ = v_a_1469_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_tail_1473_);
lean_inc(v_head_1472_);
lean_dec(v_a_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1477_ = l_Lean_MessageData_ofSyntax(v_head_1472_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v_a_1470_);
lean_ctor_set(v___x_1475_, 0, v___x_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_a_1470_);
v___x_1479_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v_a_1469_ = v_tail_1473_;
v_a_1470_ = v___x_1479_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2));
v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(lean_object* v_goal_1489_, lean_object* v_idents_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_u_1496_; lean_object* v_00_u03c3s_1497_; lean_object* v_hyps_1498_; lean_object* v_target_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_u_1496_ = lean_ctor_get(v_goal_1489_, 0);
v_00_u03c3s_1497_ = lean_ctor_get(v_goal_1489_, 1);
v_hyps_1498_ = lean_ctor_get(v_goal_1489_, 2);
v_target_1499_ = lean_ctor_get(v_goal_1489_, 3);
v___x_1500_ = l_Lean_NameSet_empty;
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_idents_1490_);
lean_inc_ref(v_hyps_1498_);
v___x_1502_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_hyps_1498_, v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1551_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1551_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1551_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_fst_1507_; lean_object* v_snd_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1550_; 
v_fst_1507_ = lean_ctor_get(v_a_1503_, 0);
v_snd_1508_ = lean_ctor_get(v_a_1503_, 1);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_a_1503_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1510_ = v_a_1503_;
v_isShared_1511_ = v_isSharedCheck_1550_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_snd_1508_);
lean_inc(v_fst_1507_);
lean_dec(v_a_1503_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1550_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_snd_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1548_; 
v_snd_1517_ = lean_ctor_get(v_snd_1508_, 1);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_snd_1508_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_snd_1508_, 0);
lean_dec(v_unused_1549_);
v___x_1519_ = v_snd_1508_;
v_isShared_1520_ = v_isSharedCheck_1548_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1517_);
lean_dec(v_snd_1508_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1548_;
goto v_resetjp_1518_;
}
v___jp_1512_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1513_, 0, v_u_1496_);
lean_ctor_set(v___x_1513_, 1, v_00_u03c3s_1497_);
lean_ctor_set(v___x_1513_, 2, v_fst_1507_);
lean_ctor_set(v___x_1513_, 3, v_target_1499_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1513_);
v___x_1515_ = v___x_1505_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_array_get_size(v_snd_1517_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_nat_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_dec(v_fst_1507_);
lean_del_object(v___x_1505_);
v___x_1524_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1);
v___x_1525_ = lean_array_to_list(v_snd_1517_);
v___x_1526_ = lean_box(0);
v___x_1527_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(v___x_1525_, v___x_1526_);
v___x_1528_ = l_Lean_MessageData_ofList(v___x_1527_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 7);
lean_ctor_set(v___x_1519_, 1, v___x_1528_);
lean_ctor_set(v___x_1519_, 0, v___x_1524_);
v___x_1530_ = v___x_1519_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3);
if (v_isShared_1511_ == 0)
{
lean_ctor_set_tag(v___x_1510_, 7);
lean_ctor_set(v___x_1510_, 1, v___x_1531_);
lean_ctor_set(v___x_1510_, 0, v___x_1530_);
v___x_1533_ = v___x_1510_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v___x_1534_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1489_);
v___x_1535_ = l_Lean_MessageData_ofExpr(v___x_1534_);
v___x_1536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1533_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1536_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
else
{
lean_inc_ref(v_target_1499_);
lean_inc_ref(v_00_u03c3s_1497_);
lean_inc(v_u_1496_);
lean_del_object(v___x_1519_);
lean_dec(v_snd_1517_);
lean_del_object(v___x_1510_);
lean_dec_ref(v_goal_1489_);
goto v___jp_1512_;
}
}
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v_goal_1489_);
v_a_1552_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1502_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1502_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___boxed(lean_object* v_goal_1560_, lean_object* v_idents_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(v_goal_1560_, v_idents_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(lean_object* v_stx_1568_, lean_object* v_lctx_1569_, lean_object* v_expectedType_x3f_1570_, lean_object* v_expr_1571_, uint8_t v_isBinder_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
lean_ctor_set(v___x_1580_, 1, v_stx_1568_);
v___x_1581_ = 0;
v___x_1582_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v_lctx_1569_);
lean_ctor_set(v___x_1582_, 2, v_expectedType_x3f_1570_);
lean_ctor_set(v___x_1582_, 3, v_expr_1571_);
lean_ctor_set_uint8(v___x_1582_, sizeof(void*)*4, v_isBinder_1572_);
lean_ctor_set_uint8(v___x_1582_, sizeof(void*)*4 + 1, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1583_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed(lean_object* v_stx_1586_, lean_object* v_lctx_1587_, lean_object* v_expectedType_x3f_1588_, lean_object* v_expr_1589_, lean_object* v_isBinder_1590_, lean_object* v_x_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v_isBinder_boxed_1597_; lean_object* v_res_1598_; 
v_isBinder_boxed_1597_ = lean_unbox(v_isBinder_1590_);
v_res_1598_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(v_stx_1586_, v_lctx_1587_, v_expectedType_x3f_1588_, v_expr_1589_, v_isBinder_boxed_1597_, v_x_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(lean_object* v___x_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1599_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed(lean_object* v___x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(v___x_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(lean_object* v___x_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1613_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed(lean_object* v___x_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(v___x_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1626_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_unsigned_to_nat(32u);
v___x_1628_ = lean_mk_empty_array_with_capacity(v___x_1627_);
v___x_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1630_ = ((size_t)5ULL);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = lean_unsigned_to_nat(32u);
v___x_1633_ = lean_mk_empty_array_with_capacity(v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0);
v___x_1635_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
lean_ctor_set(v___x_1635_, 1, v___x_1633_);
lean_ctor_set(v___x_1635_, 2, v___x_1631_);
lean_ctor_set(v___x_1635_, 3, v___x_1631_);
lean_ctor_set_usize(v___x_1635_, 4, v___x_1630_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v_infoState_1639_; lean_object* v_trees_1640_; lean_object* v___x_1641_; lean_object* v_infoState_1642_; lean_object* v_env_1643_; lean_object* v_nextMacroScope_1644_; lean_object* v_ngen_1645_; lean_object* v_auxDeclNGen_1646_; lean_object* v_traceState_1647_; lean_object* v_cache_1648_; lean_object* v_messages_1649_; lean_object* v_snapshotTasks_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1671_; 
v___x_1638_ = lean_st_ref_get(v___y_1636_);
v_infoState_1639_ = lean_ctor_get(v___x_1638_, 7);
lean_inc_ref(v_infoState_1639_);
lean_dec(v___x_1638_);
v_trees_1640_ = lean_ctor_get(v_infoState_1639_, 2);
lean_inc_ref(v_trees_1640_);
lean_dec_ref(v_infoState_1639_);
v___x_1641_ = lean_st_ref_take(v___y_1636_);
v_infoState_1642_ = lean_ctor_get(v___x_1641_, 7);
v_env_1643_ = lean_ctor_get(v___x_1641_, 0);
v_nextMacroScope_1644_ = lean_ctor_get(v___x_1641_, 1);
v_ngen_1645_ = lean_ctor_get(v___x_1641_, 2);
v_auxDeclNGen_1646_ = lean_ctor_get(v___x_1641_, 3);
v_traceState_1647_ = lean_ctor_get(v___x_1641_, 4);
v_cache_1648_ = lean_ctor_get(v___x_1641_, 5);
v_messages_1649_ = lean_ctor_get(v___x_1641_, 6);
v_snapshotTasks_1650_ = lean_ctor_get(v___x_1641_, 8);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1652_ = v___x_1641_;
v_isShared_1653_ = v_isSharedCheck_1671_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_snapshotTasks_1650_);
lean_inc(v_infoState_1642_);
lean_inc(v_messages_1649_);
lean_inc(v_cache_1648_);
lean_inc(v_traceState_1647_);
lean_inc(v_auxDeclNGen_1646_);
lean_inc(v_ngen_1645_);
lean_inc(v_nextMacroScope_1644_);
lean_inc(v_env_1643_);
lean_dec(v___x_1641_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1671_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
uint8_t v_enabled_1654_; lean_object* v_assignment_1655_; lean_object* v_lazyAssignment_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1669_; 
v_enabled_1654_ = lean_ctor_get_uint8(v_infoState_1642_, sizeof(void*)*3);
v_assignment_1655_ = lean_ctor_get(v_infoState_1642_, 0);
v_lazyAssignment_1656_ = lean_ctor_get(v_infoState_1642_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_infoState_1642_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v_infoState_1642_, 2);
lean_dec(v_unused_1670_);
v___x_1658_ = v_infoState_1642_;
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_lazyAssignment_1656_);
lean_inc(v_assignment_1655_);
lean_dec(v_infoState_1642_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 2, v___x_1660_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_assignment_1655_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_lazyAssignment_1656_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v___x_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1668_, sizeof(void*)*3, v_enabled_1654_);
v___x_1662_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 7, v___x_1662_);
v___x_1664_ = v___x_1652_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_env_1643_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_nextMacroScope_1644_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_ngen_1645_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_auxDeclNGen_1646_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_traceState_1647_);
lean_ctor_set(v_reuseFailAlloc_1667_, 5, v_cache_1648_);
lean_ctor_set(v_reuseFailAlloc_1667_, 6, v_messages_1649_);
lean_ctor_set(v_reuseFailAlloc_1667_, 7, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1667_, 8, v_snapshotTasks_1650_);
v___x_1664_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_st_ref_set(v___y_1636_, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v_trees_1640_);
return v___x_1666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___boxed(lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1672_);
lean_dec(v___y_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(lean_object* v_mkInfoOnError_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___f_1680_, lean_object* v_mkInfo_1681_, lean_object* v_a_x3f_1682_){
_start:
{
if (lean_obj_tag(v_a_x3f_1682_) == 0)
{
lean_object* v___x_1684_; 
lean_dec_ref(v_mkInfo_1681_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
v___x_1684_ = lean_apply_5(v_mkInfoOnError_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, lean_box(0));
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_a_1685_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
v___x_1687_ = lean_apply_6(v___f_1680_, v___x_1686_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, lean_box(0));
return v___x_1687_;
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v___f_1680_);
v_a_1688_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1684_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1684_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_val_1696_; lean_object* v___x_1697_; 
lean_dec_ref(v_mkInfoOnError_1675_);
v_val_1696_ = lean_ctor_get(v_a_x3f_1682_, 0);
lean_inc(v_val_1696_);
lean_dec_ref(v_a_x3f_1682_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
v___x_1697_ = lean_apply_6(v_mkInfo_1681_, v_val_1696_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, lean_box(0));
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1697_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
v___x_1699_ = lean_apply_6(v___f_1680_, v_a_1698_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, lean_box(0));
return v___x_1699_;
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec_ref(v___f_1680_);
v_a_1700_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1697_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1697_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1___boxed(lean_object* v_mkInfoOnError_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___f_1713_, lean_object* v_mkInfo_1714_, lean_object* v_a_x3f_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___f_1713_, v_mkInfo_1714_, v_a_x3f_1715_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(lean_object* v_a_1718_, lean_object* v_info_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v_env_1726_; lean_object* v_nextMacroScope_1727_; lean_object* v_ngen_1728_; lean_object* v_auxDeclNGen_1729_; lean_object* v_traceState_1730_; lean_object* v_cache_1731_; lean_object* v_messages_1732_; lean_object* v_infoState_1733_; lean_object* v_snapshotTasks_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1780_; 
v___x_1725_ = lean_st_ref_take(v___y_1723_);
v_env_1726_ = lean_ctor_get(v___x_1725_, 0);
v_nextMacroScope_1727_ = lean_ctor_get(v___x_1725_, 1);
v_ngen_1728_ = lean_ctor_get(v___x_1725_, 2);
v_auxDeclNGen_1729_ = lean_ctor_get(v___x_1725_, 3);
v_traceState_1730_ = lean_ctor_get(v___x_1725_, 4);
v_cache_1731_ = lean_ctor_get(v___x_1725_, 5);
v_messages_1732_ = lean_ctor_get(v___x_1725_, 6);
v_infoState_1733_ = lean_ctor_get(v___x_1725_, 7);
v_snapshotTasks_1734_ = lean_ctor_get(v___x_1725_, 8);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1736_ = v___x_1725_;
v_isShared_1737_ = v_isSharedCheck_1780_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_snapshotTasks_1734_);
lean_inc(v_infoState_1733_);
lean_inc(v_messages_1732_);
lean_inc(v_cache_1731_);
lean_inc(v_traceState_1730_);
lean_inc(v_auxDeclNGen_1729_);
lean_inc(v_ngen_1728_);
lean_inc(v_nextMacroScope_1727_);
lean_inc(v_env_1726_);
lean_dec(v___x_1725_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1780_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___y_1739_; 
if (lean_obj_tag(v_info_1719_) == 0)
{
uint8_t v_enabled_1746_; lean_object* v_assignment_1747_; lean_object* v_lazyAssignment_1748_; lean_object* v_trees_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1759_; 
v_enabled_1746_ = lean_ctor_get_uint8(v_infoState_1733_, sizeof(void*)*3);
v_assignment_1747_ = lean_ctor_get(v_infoState_1733_, 0);
v_lazyAssignment_1748_ = lean_ctor_get(v_infoState_1733_, 1);
v_trees_1749_ = lean_ctor_get(v_infoState_1733_, 2);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_infoState_1733_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1751_ = v_infoState_1733_;
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_trees_1749_);
lean_inc(v_lazyAssignment_1748_);
lean_inc(v_assignment_1747_);
lean_dec(v_infoState_1733_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1759_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_val_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
v_val_1753_ = lean_ctor_get(v_info_1719_, 0);
lean_inc(v_val_1753_);
lean_dec_ref(v_info_1719_);
v___x_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_val_1753_);
lean_ctor_set(v___x_1754_, 1, v_trees_1749_);
v___x_1755_ = l_Lean_PersistentArray_push___redArg(v_a_1718_, v___x_1754_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 2, v___x_1755_);
v___x_1757_ = v___x_1751_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_assignment_1747_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_lazyAssignment_1748_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v___x_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1758_, sizeof(void*)*3, v_enabled_1746_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
v___y_1739_ = v___x_1757_;
goto v___jp_1738_;
}
}
}
else
{
uint8_t v_enabled_1760_; lean_object* v_assignment_1761_; lean_object* v_lazyAssignment_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1778_; 
v_enabled_1760_ = lean_ctor_get_uint8(v_infoState_1733_, sizeof(void*)*3);
v_assignment_1761_ = lean_ctor_get(v_infoState_1733_, 0);
v_lazyAssignment_1762_ = lean_ctor_get(v_infoState_1733_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_infoState_1733_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v_infoState_1733_, 2);
lean_dec(v_unused_1779_);
v___x_1764_ = v_infoState_1733_;
v_isShared_1765_ = v_isSharedCheck_1778_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_lazyAssignment_1762_);
lean_inc(v_assignment_1761_);
lean_dec(v_infoState_1733_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1778_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_val_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1777_; 
v_val_1766_ = lean_ctor_get(v_info_1719_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_info_1719_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1768_ = v_info_1719_;
v_isShared_1769_ = v_isSharedCheck_1777_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_val_1766_);
lean_dec(v_info_1719_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1777_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 2);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_val_1766_);
v___x_1771_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = l_Lean_PersistentArray_push___redArg(v_a_1718_, v___x_1771_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 2, v___x_1772_);
v___x_1774_ = v___x_1764_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_assignment_1761_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_lazyAssignment_1762_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v___x_1772_);
lean_ctor_set_uint8(v_reuseFailAlloc_1775_, sizeof(void*)*3, v_enabled_1760_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
v___y_1739_ = v___x_1774_;
goto v___jp_1738_;
}
}
}
}
}
v___jp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 7, v___y_1739_);
v___x_1741_ = v___x_1736_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_env_1726_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_nextMacroScope_1727_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_ngen_1728_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_auxDeclNGen_1729_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_traceState_1730_);
lean_ctor_set(v_reuseFailAlloc_1745_, 5, v_cache_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 6, v_messages_1732_);
lean_ctor_set(v_reuseFailAlloc_1745_, 7, v___y_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 8, v_snapshotTasks_1734_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = lean_st_ref_set(v___y_1723_, v___x_1741_);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed(lean_object* v_a_1781_, lean_object* v_info_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(v_a_1781_, v_info_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(lean_object* v_x_1789_, lean_object* v_mkInfo_1790_, lean_object* v_mkInfoOnError_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v_infoState_1798_; uint8_t v_enabled_1799_; 
v___x_1797_ = lean_st_ref_get(v___y_1795_);
v_infoState_1798_ = lean_ctor_get(v___x_1797_, 7);
lean_inc_ref(v_infoState_1798_);
lean_dec(v___x_1797_);
v_enabled_1799_ = lean_ctor_get_uint8(v_infoState_1798_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1798_);
if (v_enabled_1799_ == 0)
{
lean_object* v___x_1800_; 
lean_dec_ref(v_mkInfoOnError_1791_);
lean_dec_ref(v_mkInfo_1790_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
v___x_1800_ = lean_apply_5(v_x_1789_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, lean_box(0));
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; lean_object* v_a_1802_; lean_object* v___f_1803_; lean_object* v_r_1804_; 
v___x_1801_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1795_);
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref(v___x_1801_);
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1803_, 0, v_a_1802_);
lean_inc(v___y_1795_);
lean_inc_ref(v___y_1794_);
lean_inc(v___y_1793_);
lean_inc_ref(v___y_1792_);
v_r_1804_ = lean_apply_5(v_x_1789_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, lean_box(0));
if (lean_obj_tag(v_r_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1829_; 
v_a_1805_ = lean_ctor_get(v_r_1804_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_r_1804_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1807_ = v_r_1804_;
v_isShared_1808_ = v_isSharedCheck_1829_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v_r_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1829_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
lean_inc(v_a_1805_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 1);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___f_1803_, v_mkInfo_1790_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v___x_1811_, 0);
lean_dec(v_unused_1819_);
v___x_1813_ = v___x_1811_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_dec(v___x_1811_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v_a_1805_);
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1805_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_a_1805_);
v_a_1820_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1811_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1811_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_a_1830_ = lean_ctor_get(v_r_1804_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v_r_1804_);
v___x_1831_ = lean_box(0);
v___x_1832_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___f_1803_, v_mkInfo_1790_, v___x_1831_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; 
v_unused_1840_ = lean_ctor_get(v___x_1832_, 0);
lean_dec(v_unused_1840_);
v___x_1834_ = v___x_1832_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_dec(v___x_1832_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set_tag(v___x_1834_, 1);
lean_ctor_set(v___x_1834_, 0, v_a_1830_);
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1830_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1830_);
v_a_1841_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1832_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1832_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___boxed(lean_object* v_x_1849_, lean_object* v_mkInfo_1850_, lean_object* v_mkInfoOnError_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_1849_, v_mkInfo_1850_, v_mkInfoOnError_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object* v_stx_1860_, lean_object* v_lctx_1861_, lean_object* v_expr_1862_, lean_object* v_expectedType_x3f_1863_, uint8_t v_isBinder_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; lean_object* v___f_1871_; lean_object* v___f_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; 
v___x_1870_ = lean_box(v_isBinder_1864_);
lean_inc(v_expectedType_x3f_1863_);
lean_inc_ref(v_lctx_1861_);
lean_inc(v_stx_1860_);
v___f_1871_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1871_, 0, v_stx_1860_);
lean_closure_set(v___f_1871_, 1, v_lctx_1861_);
lean_closure_set(v___f_1871_, 2, v_expectedType_x3f_1863_);
lean_closure_set(v___f_1871_, 3, v_expr_1862_);
lean_closure_set(v___f_1871_, 4, v___x_1870_);
v___f_1872_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0));
v___x_1873_ = lean_box(0);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
lean_ctor_set(v___x_1874_, 1, v_stx_1860_);
v___x_1875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_lctx_1861_);
lean_ctor_set(v___x_1875_, 2, v_expectedType_x3f_1863_);
v___x_1876_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1877_, 0, v___x_1876_);
v___x_1878_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v___f_1872_, v___f_1871_, v___f_1877_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed(lean_object* v_stx_1879_, lean_object* v_lctx_1880_, lean_object* v_expr_1881_, lean_object* v_expectedType_x3f_1882_, lean_object* v_isBinder_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
uint8_t v_isBinder_boxed_1889_; lean_object* v_res_1890_; 
v_isBinder_boxed_1889_ = lean_unbox(v_isBinder_1883_);
v_res_1890_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_stx_1879_, v_lctx_1880_, v_expr_1881_, v_expectedType_x3f_1882_, v_isBinder_boxed_1889_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___boxed(lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(lean_object* v_00_u03b1_1903_, lean_object* v_x_1904_, lean_object* v_mkInfo_1905_, lean_object* v_mkInfoOnError_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_1904_, v_mkInfo_1905_, v_mkInfoOnError_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_x_1914_, lean_object* v_mkInfo_1915_, lean_object* v_mkInfoOnError_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(v_00_u03b1_1913_, v_x_1914_, v_mkInfo_1915_, v_mkInfoOnError_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object* v_stx_1929_, lean_object* v_00_u03c3s_1930_, lean_object* v_hyp_1931_, uint8_t v_isBinder_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1));
v___x_1939_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_1938_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v_lctx_1941_; lean_object* v_name_1942_; lean_object* v_uniq_1943_; lean_object* v_p_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref(v___x_1939_);
v_lctx_1941_ = lean_ctor_get(v_a_1933_, 2);
v_name_1942_ = lean_ctor_get(v_hyp_1931_, 0);
lean_inc(v_name_1942_);
v_uniq_1943_ = lean_ctor_get(v_hyp_1931_, 1);
lean_inc_n(v_uniq_1943_, 2);
v_p_1944_ = lean_ctor_get(v_hyp_1931_, 2);
lean_inc_ref(v_p_1944_);
lean_dec_ref(v_hyp_1931_);
v___x_1945_ = l_Lean_mkAppB(v_a_1940_, v_00_u03c3s_1930_, v_p_1944_);
v___x_1946_ = 0;
v___x_1947_ = 0;
lean_inc_ref(v___x_1945_);
lean_inc_ref(v_lctx_1941_);
v___x_1948_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1941_, v_uniq_1943_, v_name_1942_, v___x_1945_, v___x_1946_, v___x_1947_);
v___x_1949_ = l_Lean_Expr_fvar___override(v_uniq_1943_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1945_);
v___x_1951_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_stx_1929_, v___x_1948_, v___x_1949_, v___x_1950_, v_isBinder_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_1951_;
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec_ref(v_hyp_1931_);
lean_dec_ref(v_00_u03c3s_1930_);
lean_dec(v_stx_1929_);
v_a_1952_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1939_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1939_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed(lean_object* v_stx_1960_, lean_object* v_00_u03c3s_1961_, lean_object* v_hyp_1962_, lean_object* v_isBinder_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
uint8_t v_isBinder_boxed_1969_; lean_object* v_res_1970_; 
v_isBinder_boxed_1969_ = lean_unbox(v_isBinder_1963_);
v_res_1970_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_stx_1960_, v_00_u03c3s_1961_, v_hyp_1962_, v_isBinder_boxed_1969_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
return v_res_1970_;
}
}
lean_object* runtime_initialize_Std_Do_SPred_DerivedLaws(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_ProofMode(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
