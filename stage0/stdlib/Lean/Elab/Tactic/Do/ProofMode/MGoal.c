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
lean_object* l_Lean_Meta_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v_pre_96_, 2);
lean_dec(v_pre_97_);
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
lean_dec_ref(v_fn_94_);
lean_dec_ref_known(v_fn_93_, 2);
lean_dec_ref_known(v_x_92_, 2);
v___x_138_ = lean_box(0);
return v___x_138_;
}
}
else
{
lean_object* v___x_139_; 
lean_dec_ref_known(v_x_92_, 2);
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
lean_dec_ref_known(v___x_159_, 1);
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
lean_dec_ref_known(v_declName_175_, 2);
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
lean_dec_ref_known(v_declName_175_, 2);
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
lean_dec_ref_known(v___x_252_, 1);
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
lean_dec_ref_known(v___x_259_, 1);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(lean_object* v_a_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_fst_316_; lean_object* v_snd_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_349_; 
v_fst_316_ = lean_ctor_get(v_a_310_, 0);
v_snd_317_ = lean_ctor_get(v_a_310_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_349_ == 0)
{
v___x_319_ = v_a_310_;
v_isShared_320_ = v_isSharedCheck_349_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_snd_317_);
lean_inc(v_fst_316_);
lean_dec(v_a_310_);
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
lean_dec_ref_known(v___x_334_, 1);
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
v_a_310_ = v___x_338_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg___boxed(lean_object* v_a_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
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
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_a_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v___x_366_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(lean_object* v_inst_400_, lean_object* v_a_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___boxed(lean_object* v_inst_408_, lean_object* v_a_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(v_inst_408_, v_a_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object* v_e_416_){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_417_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1));
v___x_418_ = lean_unsigned_to_nat(3u);
v___x_419_ = l_Lean_Expr_isAppOfArity(v_e_416_, v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
v___x_420_ = lean_box(0);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_421_ = lean_box(0);
v___x_422_ = l_Lean_Expr_appFn_x21(v_e_416_);
v___x_423_ = l_Lean_Expr_appFn_x21(v___x_422_);
v___x_424_ = l_Lean_Expr_appArg_x21(v___x_423_);
lean_dec_ref(v___x_423_);
v___x_425_ = l_Lean_Expr_appArg_x21(v___x_422_);
lean_dec_ref(v___x_422_);
v___x_426_ = l_Lean_Expr_appArg_x21(v_e_416_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_424_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_Expr_getAppFn(v_e_416_);
v___x_430_ = l_Lean_Expr_constLevels_x21(v___x_429_);
lean_dec_ref(v___x_429_);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = l_List_get_x21Internal___redArg(v___x_421_, v___x_430_, v___x_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_428_);
v___x_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f___boxed(lean_object* v_e_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_435_);
lean_dec_ref(v_e_435_);
return v_res_436_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1));
v___x_442_ = l_Lean_Expr_const___override(v___x_441_, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2);
v___x_444_ = lean_box(0);
v___x_445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_443_);
lean_ctor_set(v___x_445_, 2, v___x_443_);
lean_ctor_set(v___x_445_, 3, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default(void){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal(void){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default;
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object* v_expr_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_456_ = l_Lean_Expr_consumeMData(v_expr_455_);
v___x_457_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2));
v___x_458_ = lean_unsigned_to_nat(3u);
v___x_459_ = l_Lean_Expr_isAppOfArity(v___x_456_, v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec_ref(v___x_456_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_461_ = lean_box(0);
v___x_462_ = l_Lean_Expr_appFn_x21(v___x_456_);
v___x_463_ = l_Lean_Expr_appFn_x21(v___x_462_);
v___x_464_ = l_Lean_Expr_appArg_x21(v___x_463_);
lean_dec_ref(v___x_463_);
v___x_465_ = l_Lean_Expr_appArg_x21(v___x_462_);
lean_dec_ref(v___x_462_);
v___x_466_ = l_Lean_Expr_appArg_x21(v___x_456_);
lean_dec_ref(v___x_456_);
v___x_467_ = l_Lean_Expr_getAppFn_x27(v_expr_455_);
v___x_468_ = l_Lean_Expr_constLevels_x21(v___x_467_);
lean_dec_ref(v___x_467_);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = l_List_get_x21Internal___redArg(v___x_461_, v___x_468_, v___x_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_464_);
lean_ctor_set(v___x_471_, 2, v___x_465_);
lean_ctor_set(v___x_471_, 3, v___x_466_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___boxed(lean_object* v_expr_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_expr_473_);
lean_dec_ref(v_expr_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(lean_object* v_e_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_478_; uint8_t v___x_479_; 
v___x_478_ = l_Lean_Expr_hasMVar(v_e_475_);
v___x_479_ = lean_bool_not(v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v_mctx_481_; lean_object* v___x_482_; lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_485_; lean_object* v_cache_486_; lean_object* v_zetaDeltaFVarIds_487_; lean_object* v_postponed_488_; lean_object* v_diag_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_498_; 
v___x_480_ = lean_st_ref_get(v___y_476_);
v_mctx_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_mctx_481_);
lean_dec(v___x_480_);
v___x_482_ = l_Lean_instantiateMVarsCore(v_mctx_481_, v_e_475_);
v_fst_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_fst_483_);
v_snd_484_ = lean_ctor_get(v___x_482_, 1);
lean_inc(v_snd_484_);
lean_dec_ref(v___x_482_);
v___x_485_ = lean_st_ref_take(v___y_476_);
v_cache_486_ = lean_ctor_get(v___x_485_, 1);
v_zetaDeltaFVarIds_487_ = lean_ctor_get(v___x_485_, 2);
v_postponed_488_ = lean_ctor_get(v___x_485_, 3);
v_diag_489_ = lean_ctor_get(v___x_485_, 4);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v___x_485_, 0);
lean_dec(v_unused_499_);
v___x_491_ = v___x_485_;
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_diag_489_);
lean_inc(v_postponed_488_);
lean_inc(v_zetaDeltaFVarIds_487_);
lean_inc(v_cache_486_);
lean_dec(v___x_485_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_snd_484_);
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_snd_484_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_cache_486_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_zetaDeltaFVarIds_487_);
lean_ctor_set(v_reuseFailAlloc_497_, 3, v_postponed_488_);
lean_ctor_set(v_reuseFailAlloc_497_, 4, v_diag_489_);
v___x_494_ = v_reuseFailAlloc_497_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_st_ref_set(v___y_476_, v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v_fst_483_);
return v___x_496_;
}
}
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v_e_475_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg___boxed(lean_object* v_e_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_e_501_, v___y_502_);
lean_dec(v___y_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(lean_object* v_e_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_e_505_, v___y_511_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___boxed(lean_object* v_e_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(v_e_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(lean_object* v_msgData_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v_env_534_; lean_object* v___x_535_; lean_object* v_mctx_536_; lean_object* v_lctx_537_; lean_object* v_options_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_533_ = lean_st_ref_get(v___y_531_);
v_env_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc_ref(v_env_534_);
lean_dec(v___x_533_);
v___x_535_ = lean_st_ref_get(v___y_529_);
v_mctx_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc_ref(v_mctx_536_);
lean_dec(v___x_535_);
v_lctx_537_ = lean_ctor_get(v___y_528_, 2);
v_options_538_ = lean_ctor_get(v___y_530_, 2);
lean_inc_ref(v_options_538_);
lean_inc_ref(v_lctx_537_);
v___x_539_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_539_, 0, v_env_534_);
lean_ctor_set(v___x_539_, 1, v_mctx_536_);
lean_ctor_set(v___x_539_, 2, v_lctx_537_);
lean_ctor_set(v___x_539_, 3, v_options_538_);
v___x_540_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v_msgData_527_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1___boxed(lean_object* v_msgData_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msgData_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_ref_555_; lean_object* v___x_556_; lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_565_; 
v_ref_555_ = lean_ctor_get(v___y_552_, 5);
v___x_556_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_565_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_565_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
lean_inc(v_ref_555_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_ref_555_);
lean_ctor_set(v___x_561_, 1, v_a_557_);
if (v_isShared_560_ == 0)
{
lean_ctor_set_tag(v___x_559_, 1);
lean_ctor_set(v___x_559_, 0, v___x_561_);
v___x_563_ = v___x_559_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg___boxed(lean_object* v_msg_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v_msg_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0));
v___x_575_ = l_Lean_stringToMessageData(v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_577_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_n(v_a_586_, 2);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = l_Lean_MVarId_getType(v_a_586_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_602_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_a_588_, v_a_581_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_602_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_602_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_602_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_590_);
lean_dec(v_a_590_);
if (lean_obj_tag(v___x_594_) == 1)
{
lean_object* v_val_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_val_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_a_586_);
lean_ctor_set(v___x_596_, 1, v_val_595_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_596_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v___x_594_);
lean_del_object(v___x_592_);
lean_dec(v_a_586_);
v___x_600_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1);
v___x_601_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v___x_600_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
return v___x_601_;
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_a_586_);
v_a_603_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_587_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_587_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_a_611_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_585_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_585_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___boxed(lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(lean_object* v_00_u03b1_629_, lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v_msg_630_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___boxed(lean_object* v_00_u03b1_641_, lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(v_00_u03b1_641_, v_msg_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(lean_object* v_goal_659_){
_start:
{
lean_object* v_u_660_; lean_object* v_00_u03c3s_661_; lean_object* v_hyps_662_; lean_object* v_target_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_u_660_ = lean_ctor_get(v_goal_659_, 0);
lean_inc(v_u_660_);
v_00_u03c3s_661_ = lean_ctor_get(v_goal_659_, 1);
lean_inc_ref(v_00_u03c3s_661_);
v_hyps_662_ = lean_ctor_get(v_goal_659_, 2);
lean_inc_ref(v_hyps_662_);
v_target_663_ = lean_ctor_get(v_goal_659_, 3);
lean_inc_ref(v_target_663_);
lean_dec_ref(v_goal_659_);
v___x_664_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1));
v___x_665_ = lean_box(0);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v_u_660_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_mkConst(v___x_664_, v___x_666_);
v___x_668_ = l_Lean_mkApp3(v___x_667_, v_00_u03c3s_661_, v_hyps_662_, v_target_663_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object* v_goal_669_){
_start:
{
lean_object* v_u_670_; lean_object* v_00_u03c3s_671_; lean_object* v_hyps_672_; lean_object* v_target_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_u_670_ = lean_ctor_get(v_goal_669_, 0);
lean_inc(v_u_670_);
v_00_u03c3s_671_ = lean_ctor_get(v_goal_669_, 1);
lean_inc_ref(v_00_u03c3s_671_);
v_hyps_672_ = lean_ctor_get(v_goal_669_, 2);
lean_inc_ref(v_hyps_672_);
v_target_673_ = lean_ctor_get(v_goal_669_, 3);
lean_inc_ref(v_target_673_);
lean_dec_ref(v_goal_669_);
v___x_674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2));
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v_u_670_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = l_Lean_mkConst(v___x_674_, v___x_676_);
v___x_678_ = l_Lean_mkApp3(v___x_677_, v_00_u03c3s_671_, v_hyps_672_, v_target_673_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(lean_object* v_msg_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_panic_fn_borrowed(v___x_680_, v_msg_679_);
return v___x_681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2));
v___x_686_ = lean_unsigned_to_nat(8u);
v___x_687_ = lean_unsigned_to_nat(141u);
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1));
v___x_689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0));
v___x_690_ = l_mkPanicMessageWithDecl(v___x_689_, v___x_688_, v___x_687_, v___x_686_, v___x_685_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(lean_object* v_name_691_, lean_object* v_e_692_, lean_object* v_p_693_){
_start:
{
lean_object* v___x_694_; 
lean_inc_ref(v_e_692_);
v___x_694_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_692_);
if (lean_obj_tag(v___x_694_) == 1)
{
lean_object* v_val_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_e_692_);
v_val_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_706_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_val_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_name_699_; uint8_t v___x_700_; 
v_name_699_ = lean_ctor_get(v_val_695_, 0);
v___x_700_ = lean_name_eq(v_name_699_, v_name_691_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
lean_del_object(v___x_697_);
lean_dec(v_val_695_);
lean_dec(v_p_693_);
v___x_701_ = lean_box(0);
return v___x_701_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v_p_693_);
lean_ctor_set(v___x_702_, 1, v_val_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_702_);
v___x_704_ = v___x_697_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v___x_707_; 
lean_dec(v___x_694_);
v___x_707_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_692_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v_snd_709_; lean_object* v_snd_710_; lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref(v_e_692_);
v_val_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_707_, 1);
v_snd_709_ = lean_ctor_get(v_val_708_, 1);
lean_inc(v_snd_709_);
lean_dec(v_val_708_);
v_snd_710_ = lean_ctor_get(v_snd_709_, 1);
lean_inc(v_snd_710_);
lean_dec(v_snd_709_);
v_fst_711_ = lean_ctor_get(v_snd_710_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v_snd_710_, 1);
lean_inc(v_snd_712_);
lean_dec(v_snd_710_);
v___x_713_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_p_693_);
v___x_714_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_691_, v_snd_712_, v___x_713_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_p_693_);
lean_dec(v_p_693_);
v_e_692_ = v_fst_711_;
v_p_693_ = v___x_715_;
goto _start;
}
else
{
lean_dec(v_fst_711_);
lean_dec(v_p_693_);
return v___x_714_;
}
}
else
{
lean_object* v___x_717_; 
lean_dec(v___x_707_);
lean_dec(v_p_693_);
v___x_717_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_692_);
if (lean_obj_tag(v___x_717_) == 1)
{
lean_object* v___x_718_; 
lean_dec_ref_known(v___x_717_, 1);
v___x_718_ = lean_box(0);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v___x_717_);
v___x_719_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3, &l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3);
v___x_720_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(v___x_719_);
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___boxed(lean_object* v_name_721_, lean_object* v_e_722_, lean_object* v_p_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_721_, v_e_722_, v_p_723_);
lean_dec(v_name_721_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(lean_object* v_goal_725_, lean_object* v_name_726_){
_start:
{
lean_object* v_hyps_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_hyps_727_ = lean_ctor_get(v_goal_725_, 2);
lean_inc_ref(v_hyps_727_);
lean_dec_ref(v_goal_725_);
v___x_728_ = l_Lean_SubExpr_Pos_root;
v___x_729_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_726_, v_hyps_727_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f___boxed(lean_object* v_goal_730_, lean_object* v_name_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_730_, v_name_731_);
lean_dec(v_name_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(lean_object* v_msg_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_ref_739_; lean_object* v___x_740_; lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_ref_739_ = lean_ctor_get(v___y_736_, 5);
v___x_740_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
v_a_741_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v___x_740_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_740_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_inc(v_ref_739_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_ref_739_);
lean_ctor_set(v___x_745_, 1, v_a_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 1);
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg___boxed(lean_object* v_msg_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v_msg_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_756_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_764_, uint8_t v_suppressElabErrors_765_, lean_object* v_x_766_){
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
return v___y_764_;
}
else
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_776_ = lean_string_dec_eq(v_str_769_, v___x_775_);
if (v___x_776_ == 0)
{
return v___y_764_;
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
return v___y_764_;
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
return v___y_764_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_786_ = lean_string_dec_eq(v_str_781_, v___x_785_);
if (v___x_786_ == 0)
{
return v___y_764_;
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_788_ = lean_string_dec_eq(v_str_780_, v___x_787_);
if (v___x_788_ == 0)
{
return v___y_764_;
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
return v___y_764_;
}
}
default: 
{
return v___y_764_;
}
}
}
case 0:
{
lean_object* v_str_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_str_789_ = lean_ctor_get(v_x_766_, 1);
v___x_790_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_791_ = lean_string_dec_eq(v_str_789_, v___x_790_);
if (v___x_791_ == 0)
{
return v___y_764_;
}
else
{
return v_suppressElabErrors_765_;
}
}
default: 
{
return v___y_764_;
}
}
}
else
{
return v___y_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_792_, lean_object* v_suppressElabErrors_793_, lean_object* v_x_794_){
_start:
{
uint8_t v___y_4449__boxed_795_; uint8_t v_suppressElabErrors_boxed_796_; uint8_t v_res_797_; lean_object* v_r_798_; 
v___y_4449__boxed_795_ = lean_unbox(v___y_792_);
v_suppressElabErrors_boxed_796_ = lean_unbox(v_suppressElabErrors_793_);
v_res_797_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(v___y_4449__boxed_795_, v_suppressElabErrors_boxed_796_, v_x_794_);
lean_dec(v_x_794_);
v_r_798_ = lean_box(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_799_, lean_object* v_opt_800_){
_start:
{
lean_object* v_name_801_; lean_object* v_defValue_802_; lean_object* v_map_803_; lean_object* v___x_804_; 
v_name_801_ = lean_ctor_get(v_opt_800_, 0);
v_defValue_802_ = lean_ctor_get(v_opt_800_, 1);
v_map_803_ = lean_ctor_get(v_opts_799_, 0);
v___x_804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_803_, v_name_801_);
if (lean_obj_tag(v___x_804_) == 0)
{
uint8_t v___x_805_; 
v___x_805_ = lean_unbox(v_defValue_802_);
return v___x_805_;
}
else
{
lean_object* v_val_806_; 
v_val_806_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v___x_804_, 1);
if (lean_obj_tag(v_val_806_) == 1)
{
uint8_t v_v_807_; 
v_v_807_ = lean_ctor_get_uint8(v_val_806_, 0);
lean_dec_ref_known(v_val_806_, 0);
return v_v_807_;
}
else
{
uint8_t v___x_808_; 
lean_dec(v_val_806_);
v___x_808_ = lean_unbox(v_defValue_802_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_809_, lean_object* v_opt_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_opts_809_, v_opt_810_);
lean_dec_ref(v_opt_810_);
lean_dec_ref(v_opts_809_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(lean_object* v_ref_814_, lean_object* v_msgData_815_, uint8_t v_severity_816_, uint8_t v_isSilent_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___y_824_; lean_object* v___y_825_; uint8_t v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; uint8_t v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_860_; uint8_t v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; uint8_t v___y_865_; uint8_t v___y_866_; lean_object* v___y_867_; lean_object* v___y_885_; lean_object* v___y_886_; uint8_t v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; uint8_t v___y_890_; uint8_t v___y_891_; lean_object* v___y_892_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; uint8_t v___y_899_; lean_object* v___y_900_; uint8_t v___y_901_; uint8_t v___y_902_; uint8_t v___x_907_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; uint8_t v___y_913_; uint8_t v___y_914_; uint8_t v___y_915_; uint8_t v___y_917_; uint8_t v___x_932_; 
v___x_907_ = 2;
v___x_932_ = l_Lean_instBEqMessageSeverity_beq(v_severity_816_, v___x_907_);
if (v___x_932_ == 0)
{
v___y_917_ = v___x_932_;
goto v___jp_916_;
}
else
{
uint8_t v___x_933_; 
lean_inc_ref(v_msgData_815_);
v___x_933_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_815_);
v___y_917_ = v___x_933_;
goto v___jp_916_;
}
v___jp_823_:
{
lean_object* v___x_833_; lean_object* v_currNamespace_834_; lean_object* v_openDecls_835_; lean_object* v_env_836_; lean_object* v_nextMacroScope_837_; lean_object* v_ngen_838_; lean_object* v_auxDeclNGen_839_; lean_object* v_traceState_840_; lean_object* v_cache_841_; lean_object* v_messages_842_; lean_object* v_infoState_843_; lean_object* v_snapshotTasks_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_858_; 
v___x_833_ = lean_st_ref_take(v___y_832_);
v_currNamespace_834_ = lean_ctor_get(v___y_831_, 6);
v_openDecls_835_ = lean_ctor_get(v___y_831_, 7);
v_env_836_ = lean_ctor_get(v___x_833_, 0);
v_nextMacroScope_837_ = lean_ctor_get(v___x_833_, 1);
v_ngen_838_ = lean_ctor_get(v___x_833_, 2);
v_auxDeclNGen_839_ = lean_ctor_get(v___x_833_, 3);
v_traceState_840_ = lean_ctor_get(v___x_833_, 4);
v_cache_841_ = lean_ctor_get(v___x_833_, 5);
v_messages_842_ = lean_ctor_get(v___x_833_, 6);
v_infoState_843_ = lean_ctor_get(v___x_833_, 7);
v_snapshotTasks_844_ = lean_ctor_get(v___x_833_, 8);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_858_ == 0)
{
v___x_846_ = v___x_833_;
v_isShared_847_ = v_isSharedCheck_858_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_snapshotTasks_844_);
lean_inc(v_infoState_843_);
lean_inc(v_messages_842_);
lean_inc(v_cache_841_);
lean_inc(v_traceState_840_);
lean_inc(v_auxDeclNGen_839_);
lean_inc(v_ngen_838_);
lean_inc(v_nextMacroScope_837_);
lean_inc(v_env_836_);
lean_dec(v___x_833_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_858_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
lean_inc(v_openDecls_835_);
lean_inc(v_currNamespace_834_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_currNamespace_834_);
lean_ctor_set(v___x_848_, 1, v_openDecls_835_);
v___x_849_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___y_825_);
lean_inc_ref(v___y_828_);
lean_inc_ref(v___y_827_);
v___x_850_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_850_, 0, v___y_827_);
lean_ctor_set(v___x_850_, 1, v___y_824_);
lean_ctor_set(v___x_850_, 2, v___y_830_);
lean_ctor_set(v___x_850_, 3, v___y_828_);
lean_ctor_set(v___x_850_, 4, v___x_849_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*5, v___y_829_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*5 + 1, v___y_826_);
lean_ctor_set_uint8(v___x_850_, sizeof(void*)*5 + 2, v_isSilent_817_);
v___x_851_ = l_Lean_MessageLog_add(v___x_850_, v_messages_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 6, v___x_851_);
v___x_853_ = v___x_846_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_env_836_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_nextMacroScope_837_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_ngen_838_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_auxDeclNGen_839_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_traceState_840_);
lean_ctor_set(v_reuseFailAlloc_857_, 5, v_cache_841_);
lean_ctor_set(v_reuseFailAlloc_857_, 6, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_857_, 7, v_infoState_843_);
lean_ctor_set(v_reuseFailAlloc_857_, 8, v_snapshotTasks_844_);
v___x_853_ = v_reuseFailAlloc_857_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = lean_st_ref_set(v___y_832_, v___x_853_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
}
v___jp_859_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_883_; 
v___x_868_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_815_);
v___x_869_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v___x_868_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_883_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_883_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_883_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_inc_ref_n(v___y_864_, 2);
v___x_874_ = l_Lean_FileMap_toPosition(v___y_864_, v___y_863_);
lean_dec(v___y_863_);
v___x_875_ = l_Lean_FileMap_toPosition(v___y_864_, v___y_867_);
lean_dec(v___y_867_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
v___x_877_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0));
if (v___y_866_ == 0)
{
lean_del_object(v___x_872_);
lean_dec_ref(v___y_860_);
v___y_824_ = v___x_874_;
v___y_825_ = v_a_870_;
v___y_826_ = v___y_861_;
v___y_827_ = v___y_862_;
v___y_828_ = v___x_877_;
v___y_829_ = v___y_865_;
v___y_830_ = v___x_876_;
v___y_831_ = v___y_820_;
v___y_832_ = v___y_821_;
goto v___jp_823_;
}
else
{
uint8_t v___x_878_; 
lean_inc(v_a_870_);
v___x_878_ = l_Lean_MessageData_hasTag(v___y_860_, v_a_870_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_881_; 
lean_dec_ref_known(v___x_876_, 1);
lean_dec_ref(v___x_874_);
lean_dec(v_a_870_);
v___x_879_ = lean_box(0);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_879_);
v___x_881_ = v___x_872_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_del_object(v___x_872_);
v___y_824_ = v___x_874_;
v___y_825_ = v_a_870_;
v___y_826_ = v___y_861_;
v___y_827_ = v___y_862_;
v___y_828_ = v___x_877_;
v___y_829_ = v___y_865_;
v___y_830_ = v___x_876_;
v___y_831_ = v___y_820_;
v___y_832_ = v___y_821_;
goto v___jp_823_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Syntax_getTailPos_x3f(v___y_886_, v___y_890_);
lean_dec(v___y_886_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_inc(v___y_892_);
v___y_860_ = v___y_885_;
v___y_861_ = v___y_887_;
v___y_862_ = v___y_889_;
v___y_863_ = v___y_892_;
v___y_864_ = v___y_888_;
v___y_865_ = v___y_890_;
v___y_866_ = v___y_891_;
v___y_867_ = v___y_892_;
goto v___jp_859_;
}
else
{
lean_object* v_val_894_; 
v_val_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v___x_893_, 1);
v___y_860_ = v___y_885_;
v___y_861_ = v___y_887_;
v___y_862_ = v___y_889_;
v___y_863_ = v___y_892_;
v___y_864_ = v___y_888_;
v___y_865_ = v___y_890_;
v___y_866_ = v___y_891_;
v___y_867_ = v_val_894_;
goto v___jp_859_;
}
}
v___jp_895_:
{
lean_object* v_ref_903_; lean_object* v___x_904_; 
v_ref_903_ = l_Lean_replaceRef(v_ref_814_, v___y_900_);
v___x_904_ = l_Lean_Syntax_getPos_x3f(v_ref_903_, v___y_899_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___y_885_ = v___y_896_;
v___y_886_ = v_ref_903_;
v___y_887_ = v___y_902_;
v___y_888_ = v___y_898_;
v___y_889_ = v___y_897_;
v___y_890_ = v___y_899_;
v___y_891_ = v___y_901_;
v___y_892_ = v___x_905_;
goto v___jp_884_;
}
else
{
lean_object* v_val_906_; 
v_val_906_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_904_, 1);
v___y_885_ = v___y_896_;
v___y_886_ = v_ref_903_;
v___y_887_ = v___y_902_;
v___y_888_ = v___y_898_;
v___y_889_ = v___y_897_;
v___y_890_ = v___y_899_;
v___y_891_ = v___y_901_;
v___y_892_ = v_val_906_;
goto v___jp_884_;
}
}
v___jp_908_:
{
if (v___y_915_ == 0)
{
v___y_896_ = v___y_911_;
v___y_897_ = v___y_910_;
v___y_898_ = v___y_909_;
v___y_899_ = v___y_914_;
v___y_900_ = v___y_912_;
v___y_901_ = v___y_913_;
v___y_902_ = v_severity_816_;
goto v___jp_895_;
}
else
{
v___y_896_ = v___y_911_;
v___y_897_ = v___y_910_;
v___y_898_ = v___y_909_;
v___y_899_ = v___y_914_;
v___y_900_ = v___y_912_;
v___y_901_ = v___y_913_;
v___y_902_ = v___x_907_;
goto v___jp_895_;
}
}
v___jp_916_:
{
if (v___y_917_ == 0)
{
lean_object* v_fileName_918_; lean_object* v_fileMap_919_; lean_object* v_options_920_; lean_object* v_ref_921_; uint8_t v_suppressElabErrors_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___f_925_; uint8_t v___x_926_; uint8_t v___x_927_; 
v_fileName_918_ = lean_ctor_get(v___y_820_, 0);
v_fileMap_919_ = lean_ctor_get(v___y_820_, 1);
v_options_920_ = lean_ctor_get(v___y_820_, 2);
v_ref_921_ = lean_ctor_get(v___y_820_, 5);
v_suppressElabErrors_922_ = lean_ctor_get_uint8(v___y_820_, sizeof(void*)*14 + 1);
v___x_923_ = lean_box(v___y_917_);
v___x_924_ = lean_box(v_suppressElabErrors_922_);
v___f_925_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_925_, 0, v___x_923_);
lean_closure_set(v___f_925_, 1, v___x_924_);
v___x_926_ = 1;
v___x_927_ = l_Lean_instBEqMessageSeverity_beq(v_severity_816_, v___x_926_);
if (v___x_927_ == 0)
{
v___y_909_ = v_fileMap_919_;
v___y_910_ = v_fileName_918_;
v___y_911_ = v___f_925_;
v___y_912_ = v_ref_921_;
v___y_913_ = v_suppressElabErrors_922_;
v___y_914_ = v___y_917_;
v___y_915_ = v___x_927_;
goto v___jp_908_;
}
else
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = l_Lean_warningAsError;
v___x_929_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_options_920_, v___x_928_);
v___y_909_ = v_fileMap_919_;
v___y_910_ = v_fileName_918_;
v___y_911_ = v___f_925_;
v___y_912_ = v_ref_921_;
v___y_913_ = v_suppressElabErrors_922_;
v___y_914_ = v___y_917_;
v___y_915_ = v___x_929_;
goto v___jp_908_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_msgData_815_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_934_, lean_object* v_msgData_935_, lean_object* v_severity_936_, lean_object* v_isSilent_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
uint8_t v_severity_boxed_943_; uint8_t v_isSilent_boxed_944_; lean_object* v_res_945_; 
v_severity_boxed_943_ = lean_unbox(v_severity_936_);
v_isSilent_boxed_944_ = lean_unbox(v_isSilent_937_);
v_res_945_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_934_, v_msgData_935_, v_severity_boxed_943_, v_isSilent_boxed_944_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v_ref_934_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(lean_object* v_msgData_946_, uint8_t v_severity_947_, uint8_t v_isSilent_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_ref_954_; lean_object* v___x_955_; 
v_ref_954_ = lean_ctor_get(v___y_951_, 5);
v___x_955_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_954_, v_msgData_946_, v_severity_947_, v_isSilent_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0___boxed(lean_object* v_msgData_956_, lean_object* v_severity_957_, lean_object* v_isSilent_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v_severity_boxed_964_; uint8_t v_isSilent_boxed_965_; lean_object* v_res_966_; 
v_severity_boxed_964_ = lean_unbox(v_severity_957_);
v_isSilent_boxed_965_ = lean_unbox(v_isSilent_958_);
v_res_966_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_956_, v_severity_boxed_964_, v_isSilent_boxed_965_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(lean_object* v_msgData_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = 1;
v___x_974_ = 0;
v___x_975_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_967_, v___x_973_, v___x_974_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0___boxed(lean_object* v_msgData_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v_msgData_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(lean_object* v_expr_998_, lean_object* v_expectedType_999_, uint8_t v_suppressWarning_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; uint8_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = 0;
lean_inc_ref(v_expr_998_);
v___x_1022_ = l_Lean_Meta_check(v_expr_998_, v___x_1021_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1023_; 
lean_dec_ref_known(v___x_1022_, 1);
lean_inc_ref(v_expectedType_999_);
v___x_1023_ = l_Lean_Meta_check(v_expectedType_999_, v___x_1021_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v___x_1024_; 
lean_dec_ref_known(v___x_1023_, 1);
lean_inc(v_a_1004_);
lean_inc_ref(v_a_1003_);
lean_inc(v_a_1002_);
lean_inc_ref(v_a_1001_);
lean_inc_ref(v_expr_998_);
v___x_1024_ = lean_infer_type(v_expr_998_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v___x_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc_n(v_a_1025_, 2);
lean_dec_ref_known(v___x_1024_, 1);
lean_inc_ref(v_expectedType_999_);
v___x_1026_ = l_Lean_Meta_isExprDefEqGuarded(v_a_1025_, v_expectedType_999_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; uint8_t v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = lean_unbox(v_a_1027_);
lean_dec(v_a_1027_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1029_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5);
v___x_1030_ = l_Lean_indentExpr(v_expr_998_);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_indentExpr(v_a_1025_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_indentExpr(v_expectedType_999_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1039_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
return v___x_1040_;
}
else
{
lean_dec(v_a_1025_);
v___y_1007_ = v_a_1001_;
v___y_1008_ = v_a_1002_;
v___y_1009_ = v_a_1003_;
v___y_1010_ = v_a_1004_;
goto v___jp_1006_;
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec(v_a_1025_);
lean_dec_ref(v_expectedType_999_);
lean_dec_ref(v_expr_998_);
v_a_1041_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1026_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1026_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_expectedType_999_);
lean_dec_ref(v_expr_998_);
v_a_1049_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1024_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1024_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_999_);
lean_dec_ref(v_expr_998_);
return v___x_1023_;
}
}
else
{
lean_dec_ref(v_expectedType_999_);
lean_dec_ref(v_expr_998_);
return v___x_1022_;
}
v___jp_1006_:
{
if (v_suppressWarning_1000_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1011_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1);
v___x_1012_ = l_Lean_MessageData_ofExpr(v_expr_998_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_MessageData_ofExpr(v_expectedType_999_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v___x_1017_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec_ref(v_expectedType_999_);
lean_dec_ref(v_expr_998_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___boxed(lean_object* v_expr_1057_, lean_object* v_expectedType_1058_, lean_object* v_suppressWarning_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
uint8_t v_suppressWarning_boxed_1065_; lean_object* v_res_1066_; 
v_suppressWarning_boxed_1065_ = lean_unbox(v_suppressWarning_1059_);
v_res_1066_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(v_expr_1057_, v_expectedType_1058_, v_suppressWarning_boxed_1065_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(lean_object* v_00_u03b1_1067_, lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v_msg_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___boxed(lean_object* v_00_u03b1_1075_, lean_object* v_msg_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(v_00_u03b1_1075_, v_msg_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(lean_object* v_goal_1083_, lean_object* v_prf_1084_, uint8_t v_suppressWarning_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1083_);
v___x_1092_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(v_prf_1084_, v___x_1091_, v_suppressWarning_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof___boxed(lean_object* v_goal_1093_, lean_object* v_prf_1094_, lean_object* v_suppressWarning_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
uint8_t v_suppressWarning_boxed_1101_; lean_object* v_res_1102_; 
v_suppressWarning_boxed_1101_ = lean_unbox(v_suppressWarning_1095_);
v_res_1102_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(v_goal_1093_, v_prf_1094_, v_suppressWarning_boxed_1101_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object* v_x_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2));
lean_inc(v_x_1114_);
v___x_1119_ = l_Lean_Syntax_isOfKind(v_x_1114_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4));
v___x_1121_ = l_Lean_Core_mkFreshUserName(v___x_1120_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1130_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_a_1122_);
lean_ctor_set(v___x_1126_, 1, v_x_1114_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1126_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_x_1114_);
v_a_1131_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1121_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1121_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v___x_1139_; lean_object* v_name_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1139_ = lean_unsigned_to_nat(0u);
v_name_1140_ = l_Lean_Syntax_getArg(v_x_1114_, v___x_1139_);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6));
lean_inc(v_name_1140_);
v___x_1142_ = l_Lean_Syntax_isOfKind(v_name_1140_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v_name_1140_);
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4));
v___x_1144_ = l_Lean_Core_mkFreshUserName(v___x_1143_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1149_, 0, v_a_1145_);
lean_ctor_set(v___x_1149_, 1, v_x_1114_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_x_1114_);
v_a_1154_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1144_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1144_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_x_1114_);
v___x_1162_ = l_Lean_TSyntax_getId(v_name_1140_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v_name_1140_);
v___x_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___boxed(lean_object* v_x_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_x_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(lean_object* v_as_1170_, size_t v_i_1171_, size_t v_stop_1172_, lean_object* v_b_1173_){
_start:
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_usize_dec_eq(v_i_1171_, v_stop_1172_);
if (v___x_1174_ == 0)
{
size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; lean_object* v_snd_1178_; lean_object* v_fst_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v___x_1175_ = ((size_t)1ULL);
v___x_1176_ = lean_usize_sub(v_i_1171_, v___x_1175_);
v___x_1177_ = lean_array_uget_borrowed(v_as_1170_, v___x_1176_);
v_snd_1178_ = lean_ctor_get(v___x_1177_, 1);
v_fst_1179_ = lean_ctor_get(v___x_1177_, 0);
v_fst_1180_ = lean_ctor_get(v_snd_1178_, 0);
v_snd_1181_ = lean_ctor_get(v_snd_1178_, 1);
v___x_1182_ = lean_unbox(v_snd_1181_);
lean_inc(v_fst_1180_);
lean_inc(v_fst_1179_);
v___x_1183_ = l_Lean_Expr_lam___override(v_fst_1179_, v_fst_1180_, v_b_1173_, v___x_1182_);
v_i_1171_ = v___x_1176_;
v_b_1173_ = v___x_1183_;
goto _start;
}
else
{
return v_b_1173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0___boxed(lean_object* v_as_1185_, lean_object* v_i_1186_, lean_object* v_stop_1187_, lean_object* v_b_1188_){
_start:
{
size_t v_i_boxed_1189_; size_t v_stop_boxed_1190_; lean_object* v_res_1191_; 
v_i_boxed_1189_ = lean_unbox_usize(v_i_1186_);
lean_dec(v_i_1186_);
v_stop_boxed_1190_ = lean_unbox_usize(v_stop_1187_);
lean_dec(v_stop_1187_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_as_1185_, v_i_boxed_1189_, v_stop_boxed_1190_, v_b_1188_);
lean_dec_ref(v_as_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(lean_object* v_revLams_1192_, lean_object* v_revAppArgs_1193_, lean_object* v_body_1194_){
_start:
{
uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1195_ = 0;
v___x_1196_ = l_Lean_Expr_betaRev(v_body_1194_, v_revAppArgs_1193_, v___x_1195_, v___x_1195_);
v___x_1197_ = lean_array_get_size(v_revLams_1192_);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_nat_dec_lt(v___x_1198_, v___x_1197_);
if (v___x_1199_ == 0)
{
return v___x_1196_;
}
else
{
size_t v___x_1200_; size_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_usize_of_nat(v___x_1197_);
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_revLams_1192_, v___x_1200_, v___x_1201_, v___x_1196_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap___boxed(lean_object* v_revLams_1203_, lean_object* v_revAppArgs_1204_, lean_object* v_body_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1203_, v_revAppArgs_1204_, v_body_1205_);
lean_dec_ref(v_revAppArgs_1204_);
lean_dec_ref(v_revLams_1203_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(lean_object* v_00_u03c3s_1207_, lean_object* v_revLams_1208_, lean_object* v_revAppArgs_1209_, lean_object* v_e_1210_){
_start:
{
lean_object* v___x_1211_; 
lean_inc_ref(v_e_1210_);
v___x_1211_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_1210_);
if (lean_obj_tag(v___x_1211_) == 1)
{
lean_object* v_val_1212_; lean_object* v_fst_1213_; lean_object* v___x_1214_; 
lean_dec_ref(v_e_1210_);
lean_dec_ref(v_revAppArgs_1209_);
lean_dec_ref(v_revLams_1208_);
v_val_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_val_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v_fst_1213_ = lean_ctor_get(v_val_1212_, 0);
lean_inc(v_fst_1213_);
lean_dec(v_val_1212_);
v___x_1214_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_fst_1213_, v_00_u03c3s_1207_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; 
lean_dec(v___x_1211_);
lean_inc_ref(v_e_1210_);
v___x_1215_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_1210_);
if (lean_obj_tag(v___x_1215_) == 1)
{
lean_object* v_val_1216_; lean_object* v_name_1217_; lean_object* v_uniq_1218_; lean_object* v_p_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_e_1210_);
lean_dec_ref(v_00_u03c3s_1207_);
v_val_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_val_1216_);
lean_dec_ref_known(v___x_1215_, 1);
v_name_1217_ = lean_ctor_get(v_val_1216_, 0);
v_uniq_1218_ = lean_ctor_get(v_val_1216_, 1);
v_p_1219_ = lean_ctor_get(v_val_1216_, 2);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_val_1216_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1221_ = v_val_1216_;
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_p_1219_);
lean_inc(v_uniq_1218_);
lean_inc(v_name_1217_);
lean_dec(v_val_1216_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1228_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1208_, v_revAppArgs_1209_, v_p_1219_);
lean_dec_ref(v_revAppArgs_1209_);
lean_dec_ref(v_revLams_1208_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 2, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_name_1217_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_uniq_1218_);
lean_ctor_set(v_reuseFailAlloc_1227_, 2, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1225_);
return v___x_1226_;
}
}
}
else
{
lean_object* v___x_1229_; 
lean_dec(v___x_1215_);
v___x_1229_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_1210_);
if (lean_obj_tag(v___x_1229_) == 1)
{
lean_object* v_val_1230_; lean_object* v_snd_1231_; lean_object* v_snd_1232_; lean_object* v_fst_1233_; lean_object* v_fst_1234_; lean_object* v_snd_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec_ref(v_e_1210_);
v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_val_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v_snd_1231_ = lean_ctor_get(v_val_1230_, 1);
v_snd_1232_ = lean_ctor_get(v_snd_1231_, 1);
lean_inc(v_snd_1232_);
v_fst_1233_ = lean_ctor_get(v_val_1230_, 0);
lean_inc(v_fst_1233_);
lean_dec(v_val_1230_);
v_fst_1234_ = lean_ctor_get(v_snd_1232_, 0);
lean_inc(v_fst_1234_);
v_snd_1235_ = lean_ctor_get(v_snd_1232_, 1);
lean_inc(v_snd_1235_);
lean_dec(v_snd_1232_);
lean_inc_ref(v_revAppArgs_1209_);
lean_inc_ref(v_revLams_1208_);
lean_inc_ref_n(v_00_u03c3s_1207_, 2);
v___x_1236_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1207_, v_revLams_1208_, v_revAppArgs_1209_, v_fst_1234_);
v___x_1237_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1207_, v_revLams_1208_, v_revAppArgs_1209_, v_snd_1235_);
v___x_1238_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_1233_, v_00_u03c3s_1207_, v___x_1236_, v___x_1237_);
return v___x_1238_;
}
else
{
lean_dec(v___x_1229_);
if (lean_obj_tag(v_e_1210_) == 6)
{
lean_object* v_binderName_1239_; lean_object* v_binderType_1240_; lean_object* v_body_1241_; uint8_t v_binderInfo_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v_binderName_1239_ = lean_ctor_get(v_e_1210_, 0);
lean_inc(v_binderName_1239_);
v_binderType_1240_ = lean_ctor_get(v_e_1210_, 1);
lean_inc_ref(v_binderType_1240_);
v_body_1241_ = lean_ctor_get(v_e_1210_, 2);
lean_inc_ref(v_body_1241_);
v_binderInfo_1242_ = lean_ctor_get_uint8(v_e_1210_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_1210_, 3);
v___x_1243_ = lean_array_get_size(v_revAppArgs_1209_);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_sub(v___x_1243_, v___x_1244_);
v___x_1246_ = lean_nat_dec_lt(v___x_1245_, v___x_1243_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v___x_1245_);
v___x_1247_ = lean_box(v_binderInfo_1242_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_binderType_1240_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_binderName_1239_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_array_push(v_revLams_1208_, v___x_1249_);
v_revLams_1208_ = v___x_1250_;
v_e_1210_ = v_body_1241_;
goto _start;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v_binderType_1240_);
lean_dec(v_binderName_1239_);
v___x_1252_ = lean_array_fget(v_revAppArgs_1209_, v___x_1245_);
lean_dec(v___x_1245_);
v___x_1253_ = lean_array_pop(v_revAppArgs_1209_);
v___x_1254_ = lean_expr_instantiate1(v_body_1241_, v___x_1252_);
lean_dec(v___x_1252_);
lean_dec_ref(v_body_1241_);
v_revAppArgs_1209_ = v___x_1253_;
v_e_1210_ = v___x_1254_;
goto _start;
}
}
else
{
if (lean_obj_tag(v_e_1210_) == 5)
{
lean_object* v_fn_1256_; lean_object* v_arg_1257_; lean_object* v___x_1258_; 
v_fn_1256_ = lean_ctor_get(v_e_1210_, 0);
lean_inc_ref(v_fn_1256_);
v_arg_1257_ = lean_ctor_get(v_e_1210_, 1);
lean_inc_ref(v_arg_1257_);
lean_dec_ref_known(v_e_1210_, 2);
v___x_1258_ = lean_array_push(v_revAppArgs_1209_, v_arg_1257_);
v_revAppArgs_1209_ = v___x_1258_;
v_e_1210_ = v_fn_1256_;
goto _start;
}
else
{
lean_object* v___x_1260_; 
lean_dec_ref(v_00_u03c3s_1207_);
v___x_1260_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_1208_, v_revAppArgs_1209_, v_e_1210_);
lean_dec_ref(v_revAppArgs_1209_);
lean_dec_ref(v_revLams_1208_);
return v___x_1260_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(lean_object* v_00_u03c3s_1263_, lean_object* v_hyps_1264_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0));
v___x_1266_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_1263_, v___x_1265_, v___x_1265_, v_hyps_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(lean_object* v_00_u03c3s_x27_1267_, lean_object* v_e_1268_, lean_object* v_args_1269_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = l_Lean_mkAppN(v_e_1268_, v_args_1269_);
v___x_1271_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(v_00_u03c3s_x27_1267_, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames___boxed(lean_object* v_00_u03c3s_x27_1272_, lean_object* v_e_1273_, lean_object* v_args_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(v_00_u03c3s_x27_1272_, v_e_1273_, v_args_1274_);
lean_dec_ref(v_args_1274_);
return v_res_1275_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(lean_object* v_upperBound_1279_, lean_object* v_a_1280_, lean_object* v_b_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_a_1288_; uint8_t v___x_1292_; 
v___x_1292_ = lean_nat_dec_lt(v_a_1280_, v_upperBound_1279_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_dec(v_a_1280_);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_b_1281_);
return v___x_1293_;
}
else
{
lean_object* v___x_1294_; 
lean_inc_ref(v_b_1281_);
v___x_1294_ = l_Lean_Meta_whnfR(v_b_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1));
v___x_1297_ = lean_unsigned_to_nat(3u);
v___x_1298_ = l_Lean_Expr_isAppOfArity(v_a_1295_, v___x_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
lean_dec(v_a_1295_);
v___x_1299_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1);
lean_inc_ref(v_b_1281_);
v___x_1300_ = l_Lean_MessageData_ofExpr(v_b_1281_);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1301_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec_ref_known(v___x_1302_, 1);
v_a_1288_ = v_b_1281_;
goto v___jp_1287_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v_b_1281_);
lean_dec(v_a_1280_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v___x_1311_; 
lean_dec_ref(v_b_1281_);
v___x_1311_ = l_Lean_Expr_appArg_x21(v_a_1295_);
lean_dec(v_a_1295_);
v_a_1288_ = v___x_1311_;
goto v___jp_1287_;
}
}
else
{
lean_dec_ref(v_b_1281_);
lean_dec(v_a_1280_);
return v___x_1294_;
}
}
v___jp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_nat_add(v_a_1280_, v___x_1289_);
lean_dec(v_a_1280_);
v_a_1280_ = v___x_1290_;
v_b_1281_ = v_a_1288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___boxed(lean_object* v_upperBound_1312_, lean_object* v_a_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_1312_, v_a_1313_, v_b_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v_upperBound_1312_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(lean_object* v_00_u03c3s_1321_, lean_object* v_n_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_unsigned_to_nat(0u);
v___x_1329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_n_1322_, v___x_1328_, v_00_u03c3s_1321_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_dropStateList___boxed(lean_object* v_00_u03c3s_1330_, lean_object* v_n_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(v_00_u03c3s_1330_, v_n_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_n_1331_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(lean_object* v_upperBound_1338_, lean_object* v_inst_1339_, lean_object* v_R_1340_, lean_object* v_a_1341_, lean_object* v_b_1342_, lean_object* v_c_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_1338_, v_a_1341_, v_b_1342_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___boxed(lean_object* v_upperBound_1350_, lean_object* v_inst_1351_, lean_object* v_R_1352_, lean_object* v_a_1353_, lean_object* v_b_1354_, lean_object* v_c_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(v_upperBound_1350_, v_inst_1351_, v_R_1352_, v_a_1353_, v_b_1354_, v_c_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v_upperBound_1350_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(lean_object* v_H_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_fst_1365_; lean_object* v_snd_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_fst_1365_ = lean_ctor_get(v_a_1363_, 0);
v_snd_1366_ = lean_ctor_get(v_a_1363_, 1);
v___x_1367_ = lean_array_get_size(v_snd_1366_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_nat_dec_eq(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_inc_ref(v_H_1362_);
v___x_1370_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_H_1362_);
if (lean_obj_tag(v___x_1370_) == 1)
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1379_);
v___x_1372_ = v___x_1370_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_H_1362_);
lean_ctor_set(v___x_1374_, 1, v_a_1363_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_object* v___x_1380_; 
lean_dec(v___x_1370_);
lean_inc_ref(v_H_1362_);
v___x_1380_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_H_1362_);
if (lean_obj_tag(v___x_1380_) == 1)
{
lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1429_; 
lean_inc(v_snd_1366_);
lean_inc(v_fst_1365_);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_a_1363_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1430_ = lean_ctor_get(v_a_1363_, 1);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_a_1363_, 0);
lean_dec(v_unused_1431_);
v___x_1382_ = v_a_1363_;
v_isShared_1383_ = v_isSharedCheck_1429_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v_a_1363_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1429_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_val_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1428_; 
v_val_1384_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1386_ = v___x_1380_;
v_isShared_1387_ = v_isSharedCheck_1428_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_val_1384_);
lean_dec(v___x_1380_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1428_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_name_1388_; lean_object* v_uniq_1389_; lean_object* v_p_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1427_; 
v_name_1388_ = lean_ctor_get(v_val_1384_, 0);
v_uniq_1389_ = lean_ctor_get(v_val_1384_, 1);
v_p_1390_ = lean_ctor_get(v_val_1384_, 2);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_val_1384_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1392_ = v_val_1384_;
v_isShared_1393_ = v_isSharedCheck_1427_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_p_1390_);
lean_inc(v_uniq_1389_);
lean_inc(v_name_1388_);
lean_dec(v_val_1384_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1427_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_idents_1395_; uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_Name_hasMacroScopes(v_name_1388_);
if (v___x_1425_ == 0)
{
uint8_t v___x_1426_; 
v___x_1426_ = l_Lean_NameSet_contains(v_fst_1365_, v_name_1388_);
if (v___x_1426_ == 0)
{
lean_del_object(v___x_1392_);
lean_dec_ref(v_p_1390_);
lean_dec(v_uniq_1389_);
v_idents_1395_ = v_snd_1366_;
goto v___jp_1394_;
}
else
{
goto v___jp_1404_;
}
}
else
{
goto v___jp_1404_;
}
v___jp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = l_Lean_NameSet_insert(v_fst_1365_, v_name_1388_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 1, v_idents_1395_);
lean_ctor_set(v___x_1382_, 0, v___x_1396_);
v___x_1398_ = v___x_1382_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_idents_1395_);
v___x_1398_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_H_1362_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set_tag(v___x_1386_, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1399_);
v___x_1401_ = v___x_1386_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
v___jp_1404_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1405_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2));
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_unsigned_to_nat(1u);
v___x_1408_ = lean_nat_sub(v___x_1367_, v___x_1407_);
v___x_1409_ = lean_array_get_borrowed(v___x_1406_, v_snd_1366_, v___x_1408_);
lean_dec(v___x_1408_);
lean_inc(v___x_1409_);
v___x_1410_ = l_Lean_Syntax_isOfKind(v___x_1409_, v___x_1405_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_del_object(v___x_1392_);
lean_dec_ref(v_p_1390_);
lean_dec(v_uniq_1389_);
v___x_1411_ = lean_array_pop(v_snd_1366_);
v_idents_1395_ = v___x_1411_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = l_Lean_Syntax_getArg(v___x_1409_, v___x_1368_);
v___x_1413_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6));
lean_inc(v___x_1412_);
v___x_1414_ = l_Lean_Syntax_isOfKind(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
lean_dec(v___x_1412_);
lean_del_object(v___x_1392_);
lean_dec_ref(v_p_1390_);
lean_dec(v_uniq_1389_);
v___x_1415_ = lean_array_pop(v_snd_1366_);
v_idents_1395_ = v___x_1415_;
goto v___jp_1394_;
}
else
{
lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_dec(v_name_1388_);
lean_del_object(v___x_1386_);
lean_del_object(v___x_1382_);
lean_dec_ref(v_H_1362_);
v___x_1416_ = l_Lean_TSyntax_getId(v___x_1412_);
lean_dec(v___x_1412_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1416_);
v___x_1418_ = v___x_1392_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_uniq_1389_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_p_1390_);
v___x_1418_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1419_ = lean_array_pop(v_snd_1366_);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_fst_1365_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1418_);
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
lean_ctor_set(v___x_1422_, 1, v___x_1420_);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
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
lean_object* v___x_1432_; 
lean_dec(v___x_1380_);
v___x_1432_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_H_1362_);
if (lean_obj_tag(v___x_1432_) == 1)
{
lean_object* v_val_1433_; lean_object* v_snd_1434_; lean_object* v_snd_1435_; lean_object* v_fst_1436_; lean_object* v_fst_1437_; lean_object* v_fst_1438_; lean_object* v_snd_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v_H_1362_);
v_val_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_val_1433_);
lean_dec_ref_known(v___x_1432_, 1);
v_snd_1434_ = lean_ctor_get(v_val_1433_, 1);
lean_inc(v_snd_1434_);
v_snd_1435_ = lean_ctor_get(v_snd_1434_, 1);
lean_inc(v_snd_1435_);
v_fst_1436_ = lean_ctor_get(v_val_1433_, 0);
lean_inc(v_fst_1436_);
lean_dec(v_val_1433_);
v_fst_1437_ = lean_ctor_get(v_snd_1434_, 0);
lean_inc(v_fst_1437_);
lean_dec(v_snd_1434_);
v_fst_1438_ = lean_ctor_get(v_snd_1435_, 0);
lean_inc(v_fst_1438_);
v_snd_1439_ = lean_ctor_get(v_snd_1435_, 1);
lean_inc(v_snd_1439_);
lean_dec(v_snd_1435_);
v___x_1440_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_snd_1439_, v_a_1363_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v_fst_1442_; lean_object* v_snd_1443_; lean_object* v___x_1444_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v_fst_1442_ = lean_ctor_get(v_a_1441_, 0);
lean_inc(v_fst_1442_);
v_snd_1443_ = lean_ctor_get(v_a_1441_, 1);
lean_inc(v_snd_1443_);
lean_dec(v_a_1441_);
v___x_1444_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_fst_1438_, v_snd_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1462_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1462_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1462_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v_fst_1449_; lean_object* v_snd_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1461_; 
v_fst_1449_ = lean_ctor_get(v_a_1445_, 0);
v_snd_1450_ = lean_ctor_get(v_a_1445_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_a_1445_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1452_ = v_a_1445_;
v_isShared_1453_ = v_isSharedCheck_1461_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_snd_1450_);
lean_inc(v_fst_1449_);
lean_dec(v_a_1445_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1461_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_fst_1436_, v_fst_1437_, v_fst_1449_, v_fst_1442_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_snd_1450_);
v___x_1456_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1456_);
v___x_1458_ = v___x_1447_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
else
{
lean_dec(v_fst_1442_);
lean_dec(v_fst_1437_);
lean_dec(v_fst_1436_);
return v___x_1444_;
}
}
else
{
lean_dec(v_fst_1438_);
lean_dec(v_fst_1437_);
lean_dec(v_fst_1436_);
return v___x_1440_;
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec(v___x_1432_);
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_H_1362_);
lean_ctor_set(v___x_1463_, 1, v_a_1363_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
}
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1465_, 0, v_H_1362_);
lean_ctor_set(v___x_1465_, 1, v_a_1363_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg___boxed(lean_object* v_H_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_1467_, v_a_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(lean_object* v_H_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_1471_, v_a_1472_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___boxed(lean_object* v_H_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(v_H_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec(v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
if (lean_obj_tag(v_a_1487_) == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = l_List_reverse___redArg(v_a_1488_);
return v___x_1489_;
}
else
{
lean_object* v_head_1490_; lean_object* v_tail_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1500_; 
v_head_1490_ = lean_ctor_get(v_a_1487_, 0);
v_tail_1491_ = lean_ctor_get(v_a_1487_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_a_1487_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1493_ = v_a_1487_;
v_isShared_1494_ = v_isSharedCheck_1500_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_tail_1491_);
lean_inc(v_head_1490_);
lean_dec(v_a_1487_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1500_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = l_Lean_MessageData_ofSyntax(v_head_1490_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v_a_1488_);
lean_ctor_set(v___x_1493_, 0, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1488_);
v___x_1497_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v_a_1487_ = v_tail_1491_;
v_a_1488_ = v___x_1497_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(lean_object* v_goal_1507_, lean_object* v_idents_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_u_1514_; lean_object* v_00_u03c3s_1515_; lean_object* v_hyps_1516_; lean_object* v_target_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_u_1514_ = lean_ctor_get(v_goal_1507_, 0);
v_00_u03c3s_1515_ = lean_ctor_get(v_goal_1507_, 1);
v_hyps_1516_ = lean_ctor_get(v_goal_1507_, 2);
v_target_1517_ = lean_ctor_get(v_goal_1507_, 3);
v___x_1518_ = l_Lean_NameSet_empty;
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v_idents_1508_);
lean_inc_ref(v_hyps_1516_);
v___x_1520_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_hyps_1516_, v___x_1519_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1569_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1569_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1569_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1568_; 
v_fst_1525_ = lean_ctor_get(v_a_1521_, 0);
v_snd_1526_ = lean_ctor_get(v_a_1521_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_a_1521_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1528_ = v_a_1521_;
v_isShared_1529_ = v_isSharedCheck_1568_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snd_1526_);
lean_inc(v_fst_1525_);
lean_dec(v_a_1521_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1568_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_snd_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1566_; 
v_snd_1535_ = lean_ctor_get(v_snd_1526_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_snd_1526_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v_snd_1526_, 0);
lean_dec(v_unused_1567_);
v___x_1537_ = v_snd_1526_;
v_isShared_1538_ = v_isSharedCheck_1566_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_snd_1535_);
lean_dec(v_snd_1526_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1566_;
goto v_resetjp_1536_;
}
v___jp_1530_:
{
lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1531_, 0, v_u_1514_);
lean_ctor_set(v___x_1531_, 1, v_00_u03c3s_1515_);
lean_ctor_set(v___x_1531_, 2, v_fst_1525_);
lean_ctor_set(v___x_1531_, 3, v_target_1517_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1531_);
v___x_1533_ = v___x_1523_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1539_ = lean_array_get_size(v_snd_1535_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_nat_dec_eq(v___x_1539_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_dec(v_fst_1525_);
lean_del_object(v___x_1523_);
v___x_1542_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1);
v___x_1543_ = lean_array_to_list(v_snd_1535_);
v___x_1544_ = lean_box(0);
v___x_1545_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(v___x_1543_, v___x_1544_);
v___x_1546_ = l_Lean_MessageData_ofList(v___x_1545_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 7);
lean_ctor_set(v___x_1537_, 1, v___x_1546_);
lean_ctor_set(v___x_1537_, 0, v___x_1542_);
v___x_1548_ = v___x_1537_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 7);
lean_ctor_set(v___x_1528_, 1, v___x_1549_);
lean_ctor_set(v___x_1528_, 0, v___x_1548_);
v___x_1551_ = v___x_1528_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1548_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
v___x_1552_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_1507_);
v___x_1553_ = l_Lean_MessageData_ofExpr(v___x_1552_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1551_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_1554_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
else
{
lean_inc_ref(v_target_1517_);
lean_inc_ref(v_00_u03c3s_1515_);
lean_inc(v_u_1514_);
lean_del_object(v___x_1537_);
lean_dec(v_snd_1535_);
lean_del_object(v___x_1528_);
lean_dec_ref(v_goal_1507_);
goto v___jp_1530_;
}
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v_goal_1507_);
v_a_1570_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1520_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1520_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___boxed(lean_object* v_goal_1578_, lean_object* v_idents_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(v_goal_1578_, v_idents_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(lean_object* v_stx_1586_, lean_object* v_lctx_1587_, lean_object* v_expectedType_x3f_1588_, lean_object* v_expr_1589_, uint8_t v_isBinder_1590_, lean_object* v_x_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v_stx_1586_);
v___x_1599_ = 0;
v___x_1600_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v_lctx_1587_);
lean_ctor_set(v___x_1600_, 2, v_expectedType_x3f_1588_);
lean_ctor_set(v___x_1600_, 3, v_expr_1589_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*4, v_isBinder_1590_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*4 + 1, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed(lean_object* v_stx_1604_, lean_object* v_lctx_1605_, lean_object* v_expectedType_x3f_1606_, lean_object* v_expr_1607_, lean_object* v_isBinder_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
uint8_t v_isBinder_boxed_1615_; lean_object* v_res_1616_; 
v_isBinder_boxed_1615_ = lean_unbox(v_isBinder_1608_);
v_res_1616_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(v_stx_1604_, v_lctx_1605_, v_expectedType_x3f_1606_, v_expr_1607_, v_isBinder_boxed_1615_, v_x_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(lean_object* v___x_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1617_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed(lean_object* v___x_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(v___x_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(lean_object* v___x_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1631_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed(lean_object* v___x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(v___x_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1644_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unsigned_to_nat(32u);
v___x_1646_ = lean_mk_empty_array_with_capacity(v___x_1645_);
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1648_ = ((size_t)5ULL);
v___x_1649_ = lean_unsigned_to_nat(0u);
v___x_1650_ = lean_unsigned_to_nat(32u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0);
v___x_1653_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___x_1651_);
lean_ctor_set(v___x_1653_, 2, v___x_1649_);
lean_ctor_set(v___x_1653_, 3, v___x_1649_);
lean_ctor_set_usize(v___x_1653_, 4, v___x_1648_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v_infoState_1657_; lean_object* v_trees_1658_; lean_object* v___x_1659_; lean_object* v_infoState_1660_; lean_object* v_env_1661_; lean_object* v_nextMacroScope_1662_; lean_object* v_ngen_1663_; lean_object* v_auxDeclNGen_1664_; lean_object* v_traceState_1665_; lean_object* v_cache_1666_; lean_object* v_messages_1667_; lean_object* v_snapshotTasks_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1689_; 
v___x_1656_ = lean_st_ref_get(v___y_1654_);
v_infoState_1657_ = lean_ctor_get(v___x_1656_, 7);
lean_inc_ref(v_infoState_1657_);
lean_dec(v___x_1656_);
v_trees_1658_ = lean_ctor_get(v_infoState_1657_, 2);
lean_inc_ref(v_trees_1658_);
lean_dec_ref(v_infoState_1657_);
v___x_1659_ = lean_st_ref_take(v___y_1654_);
v_infoState_1660_ = lean_ctor_get(v___x_1659_, 7);
v_env_1661_ = lean_ctor_get(v___x_1659_, 0);
v_nextMacroScope_1662_ = lean_ctor_get(v___x_1659_, 1);
v_ngen_1663_ = lean_ctor_get(v___x_1659_, 2);
v_auxDeclNGen_1664_ = lean_ctor_get(v___x_1659_, 3);
v_traceState_1665_ = lean_ctor_get(v___x_1659_, 4);
v_cache_1666_ = lean_ctor_get(v___x_1659_, 5);
v_messages_1667_ = lean_ctor_get(v___x_1659_, 6);
v_snapshotTasks_1668_ = lean_ctor_get(v___x_1659_, 8);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1670_ = v___x_1659_;
v_isShared_1671_ = v_isSharedCheck_1689_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snapshotTasks_1668_);
lean_inc(v_infoState_1660_);
lean_inc(v_messages_1667_);
lean_inc(v_cache_1666_);
lean_inc(v_traceState_1665_);
lean_inc(v_auxDeclNGen_1664_);
lean_inc(v_ngen_1663_);
lean_inc(v_nextMacroScope_1662_);
lean_inc(v_env_1661_);
lean_dec(v___x_1659_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1689_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
uint8_t v_enabled_1672_; lean_object* v_assignment_1673_; lean_object* v_lazyAssignment_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1687_; 
v_enabled_1672_ = lean_ctor_get_uint8(v_infoState_1660_, sizeof(void*)*3);
v_assignment_1673_ = lean_ctor_get(v_infoState_1660_, 0);
v_lazyAssignment_1674_ = lean_ctor_get(v_infoState_1660_, 1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_infoState_1660_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v_infoState_1660_, 2);
lean_dec(v_unused_1688_);
v___x_1676_ = v_infoState_1660_;
v_isShared_1677_ = v_isSharedCheck_1687_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_lazyAssignment_1674_);
lean_inc(v_assignment_1673_);
lean_dec(v_infoState_1660_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1687_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_obj_once(&l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1, &l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1);
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 2, v___x_1678_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_assignment_1673_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_lazyAssignment_1674_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v___x_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*3, v_enabled_1672_);
v___x_1680_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1682_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 7, v___x_1680_);
v___x_1682_ = v___x_1670_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_env_1661_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_nextMacroScope_1662_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_ngen_1663_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_auxDeclNGen_1664_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v_traceState_1665_);
lean_ctor_set(v_reuseFailAlloc_1685_, 5, v_cache_1666_);
lean_ctor_set(v_reuseFailAlloc_1685_, 6, v_messages_1667_);
lean_ctor_set(v_reuseFailAlloc_1685_, 7, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1685_, 8, v_snapshotTasks_1668_);
v___x_1682_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_st_ref_set(v___y_1654_, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_trees_1658_);
return v___x_1684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___boxed(lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1690_);
lean_dec(v___y_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(lean_object* v_mkInfoOnError_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___f_1698_, lean_object* v_mkInfo_1699_, lean_object* v_a_x3f_1700_){
_start:
{
if (lean_obj_tag(v_a_x3f_1700_) == 0)
{
lean_object* v___x_1702_; 
lean_dec_ref(v_mkInfo_1699_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
v___x_1702_ = lean_apply_5(v_mkInfoOnError_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, lean_box(0));
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_a_1703_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
v___x_1705_ = lean_apply_6(v___f_1698_, v___x_1704_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, lean_box(0));
return v___x_1705_;
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v___f_1698_);
v_a_1706_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1702_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1702_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
else
{
lean_object* v_val_1714_; lean_object* v___x_1715_; 
lean_dec_ref(v_mkInfoOnError_1693_);
v_val_1714_ = lean_ctor_get(v_a_x3f_1700_, 0);
lean_inc(v_val_1714_);
lean_dec_ref_known(v_a_x3f_1700_, 1);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
v___x_1715_ = lean_apply_6(v_mkInfo_1699_, v_val_1714_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, lean_box(0));
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1717_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
v___x_1717_ = lean_apply_6(v___f_1698_, v_a_1716_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, lean_box(0));
return v___x_1717_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v___f_1698_);
v_a_1718_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1715_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1715_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1___boxed(lean_object* v_mkInfoOnError_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___f_1731_, lean_object* v_mkInfo_1732_, lean_object* v_a_x3f_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___f_1731_, v_mkInfo_1732_, v_a_x3f_1733_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(lean_object* v_a_1736_, lean_object* v_info_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; lean_object* v_env_1744_; lean_object* v_nextMacroScope_1745_; lean_object* v_ngen_1746_; lean_object* v_auxDeclNGen_1747_; lean_object* v_traceState_1748_; lean_object* v_cache_1749_; lean_object* v_messages_1750_; lean_object* v_infoState_1751_; lean_object* v_snapshotTasks_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1798_; 
v___x_1743_ = lean_st_ref_take(v___y_1741_);
v_env_1744_ = lean_ctor_get(v___x_1743_, 0);
v_nextMacroScope_1745_ = lean_ctor_get(v___x_1743_, 1);
v_ngen_1746_ = lean_ctor_get(v___x_1743_, 2);
v_auxDeclNGen_1747_ = lean_ctor_get(v___x_1743_, 3);
v_traceState_1748_ = lean_ctor_get(v___x_1743_, 4);
v_cache_1749_ = lean_ctor_get(v___x_1743_, 5);
v_messages_1750_ = lean_ctor_get(v___x_1743_, 6);
v_infoState_1751_ = lean_ctor_get(v___x_1743_, 7);
v_snapshotTasks_1752_ = lean_ctor_get(v___x_1743_, 8);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1754_ = v___x_1743_;
v_isShared_1755_ = v_isSharedCheck_1798_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_snapshotTasks_1752_);
lean_inc(v_infoState_1751_);
lean_inc(v_messages_1750_);
lean_inc(v_cache_1749_);
lean_inc(v_traceState_1748_);
lean_inc(v_auxDeclNGen_1747_);
lean_inc(v_ngen_1746_);
lean_inc(v_nextMacroScope_1745_);
lean_inc(v_env_1744_);
lean_dec(v___x_1743_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1798_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___y_1757_; 
if (lean_obj_tag(v_info_1737_) == 0)
{
uint8_t v_enabled_1764_; lean_object* v_assignment_1765_; lean_object* v_lazyAssignment_1766_; lean_object* v_trees_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1777_; 
v_enabled_1764_ = lean_ctor_get_uint8(v_infoState_1751_, sizeof(void*)*3);
v_assignment_1765_ = lean_ctor_get(v_infoState_1751_, 0);
v_lazyAssignment_1766_ = lean_ctor_get(v_infoState_1751_, 1);
v_trees_1767_ = lean_ctor_get(v_infoState_1751_, 2);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_infoState_1751_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1769_ = v_infoState_1751_;
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_trees_1767_);
lean_inc(v_lazyAssignment_1766_);
lean_inc(v_assignment_1765_);
lean_dec(v_infoState_1751_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_val_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v_val_1771_ = lean_ctor_get(v_info_1737_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v_info_1737_, 1);
v___x_1772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_val_1771_);
lean_ctor_set(v___x_1772_, 1, v_trees_1767_);
v___x_1773_ = l_Lean_PersistentArray_push___redArg(v_a_1736_, v___x_1772_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 2, v___x_1773_);
v___x_1775_ = v___x_1769_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_assignment_1765_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_lazyAssignment_1766_);
lean_ctor_set(v_reuseFailAlloc_1776_, 2, v___x_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1776_, sizeof(void*)*3, v_enabled_1764_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
v___y_1757_ = v___x_1775_;
goto v___jp_1756_;
}
}
}
else
{
uint8_t v_enabled_1778_; lean_object* v_assignment_1779_; lean_object* v_lazyAssignment_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1796_; 
v_enabled_1778_ = lean_ctor_get_uint8(v_infoState_1751_, sizeof(void*)*3);
v_assignment_1779_ = lean_ctor_get(v_infoState_1751_, 0);
v_lazyAssignment_1780_ = lean_ctor_get(v_infoState_1751_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_infoState_1751_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_infoState_1751_, 2);
lean_dec(v_unused_1797_);
v___x_1782_ = v_infoState_1751_;
v_isShared_1783_ = v_isSharedCheck_1796_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_lazyAssignment_1780_);
lean_inc(v_assignment_1779_);
lean_dec(v_infoState_1751_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1796_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_val_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1795_; 
v_val_1784_ = lean_ctor_get(v_info_1737_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_info_1737_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1786_ = v_info_1737_;
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_val_1784_);
lean_dec(v_info_1737_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1795_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set_tag(v___x_1786_, 2);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_val_1784_);
v___x_1789_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1790_ = l_Lean_PersistentArray_push___redArg(v_a_1736_, v___x_1789_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 2, v___x_1790_);
v___x_1792_ = v___x_1782_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_assignment_1779_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_lazyAssignment_1780_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v___x_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1793_, sizeof(void*)*3, v_enabled_1778_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
v___y_1757_ = v___x_1792_;
goto v___jp_1756_;
}
}
}
}
}
v___jp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 7, v___y_1757_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_env_1744_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_nextMacroScope_1745_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_ngen_1746_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_auxDeclNGen_1747_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_traceState_1748_);
lean_ctor_set(v_reuseFailAlloc_1763_, 5, v_cache_1749_);
lean_ctor_set(v_reuseFailAlloc_1763_, 6, v_messages_1750_);
lean_ctor_set(v_reuseFailAlloc_1763_, 7, v___y_1757_);
lean_ctor_set(v_reuseFailAlloc_1763_, 8, v_snapshotTasks_1752_);
v___x_1759_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_st_ref_set(v___y_1741_, v___x_1759_);
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed(lean_object* v_a_1799_, lean_object* v_info_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(v_a_1799_, v_info_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(lean_object* v_x_1807_, lean_object* v_mkInfo_1808_, lean_object* v_mkInfoOnError_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v_infoState_1816_; uint8_t v_enabled_1817_; 
v___x_1815_ = lean_st_ref_get(v___y_1813_);
v_infoState_1816_ = lean_ctor_get(v___x_1815_, 7);
lean_inc_ref(v_infoState_1816_);
lean_dec(v___x_1815_);
v_enabled_1817_ = lean_ctor_get_uint8(v_infoState_1816_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1816_);
if (v_enabled_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref(v_mkInfoOnError_1809_);
lean_dec_ref(v_mkInfo_1808_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
v___x_1818_ = lean_apply_5(v_x_1807_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, lean_box(0));
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; lean_object* v_a_1820_; lean_object* v___f_1821_; lean_object* v_r_1822_; 
v___x_1819_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1813_);
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
v___f_1821_ = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1821_, 0, v_a_1820_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
lean_inc(v___y_1811_);
lean_inc_ref(v___y_1810_);
v_r_1822_ = lean_apply_5(v_x_1807_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, lean_box(0));
if (lean_obj_tag(v_r_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1847_; 
v_a_1823_ = lean_ctor_get(v_r_1822_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_r_1822_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1825_ = v_r_1822_;
v_isShared_1826_ = v_isSharedCheck_1847_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v_r_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1847_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
lean_inc(v_a_1823_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set_tag(v___x_1825_, 1);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___f_1821_, v_mkInfo_1808_, v___x_1828_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1837_);
v___x_1831_ = v___x_1829_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v_a_1823_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1823_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1823_);
v_a_1838_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1829_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1829_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1848_ = lean_ctor_get(v_r_1822_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v_r_1822_, 1);
v___x_1849_ = lean_box(0);
v___x_1850_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___f_1821_, v_mkInfo_1808_, v___x_1849_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1858_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set_tag(v___x_1852_, 1);
lean_ctor_set(v___x_1852_, 0, v_a_1848_);
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1848_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1848_);
v_a_1859_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1850_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1850_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___boxed(lean_object* v_x_1867_, lean_object* v_mkInfo_1868_, lean_object* v_mkInfoOnError_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_1867_, v_mkInfo_1868_, v_mkInfoOnError_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object* v_stx_1878_, lean_object* v_lctx_1879_, lean_object* v_expr_1880_, lean_object* v_expectedType_x3f_1881_, uint8_t v_isBinder_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v___f_1889_; lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; 
v___x_1888_ = lean_box(v_isBinder_1882_);
lean_inc(v_expectedType_x3f_1881_);
lean_inc_ref(v_lctx_1879_);
lean_inc(v_stx_1878_);
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed), 11, 5);
lean_closure_set(v___f_1889_, 0, v_stx_1878_);
lean_closure_set(v___f_1889_, 1, v_lctx_1879_);
lean_closure_set(v___f_1889_, 2, v_expectedType_x3f_1881_);
lean_closure_set(v___f_1889_, 3, v_expr_1880_);
lean_closure_set(v___f_1889_, 4, v___x_1888_);
v___f_1890_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0));
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v_stx_1878_);
v___x_1893_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v_lctx_1879_);
lean_ctor_set(v___x_1893_, 2, v_expectedType_x3f_1881_);
v___x_1894_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed), 6, 1);
lean_closure_set(v___f_1895_, 0, v___x_1894_);
v___x_1896_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v___f_1890_, v___f_1889_, v___f_1895_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed(lean_object* v_stx_1897_, lean_object* v_lctx_1898_, lean_object* v_expr_1899_, lean_object* v_expectedType_x3f_1900_, lean_object* v_isBinder_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
uint8_t v_isBinder_boxed_1907_; lean_object* v_res_1908_; 
v_isBinder_boxed_1907_ = lean_unbox(v_isBinder_1901_);
v_res_1908_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_stx_1897_, v_lctx_1898_, v_expr_1899_, v_expectedType_x3f_1900_, v_isBinder_boxed_1907_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___boxed(lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(lean_object* v_00_u03b1_1921_, lean_object* v_x_1922_, lean_object* v_mkInfo_1923_, lean_object* v_mkInfoOnError_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_1922_, v_mkInfo_1923_, v_mkInfoOnError_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_x_1932_, lean_object* v_mkInfo_1933_, lean_object* v_mkInfoOnError_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(v_00_u03b1_1931_, v_x_1932_, v_mkInfo_1933_, v_mkInfoOnError_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object* v_stx_1947_, lean_object* v_00_u03c3s_1948_, lean_object* v_hyp_1949_, uint8_t v_isBinder_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1));
v___x_1957_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_1956_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v_lctx_1959_; lean_object* v_name_1960_; lean_object* v_uniq_1961_; lean_object* v_p_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; uint8_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_lctx_1959_ = lean_ctor_get(v_a_1951_, 2);
v_name_1960_ = lean_ctor_get(v_hyp_1949_, 0);
lean_inc(v_name_1960_);
v_uniq_1961_ = lean_ctor_get(v_hyp_1949_, 1);
lean_inc_n(v_uniq_1961_, 2);
v_p_1962_ = lean_ctor_get(v_hyp_1949_, 2);
lean_inc_ref(v_p_1962_);
lean_dec_ref(v_hyp_1949_);
v___x_1963_ = l_Lean_mkAppB(v_a_1958_, v_00_u03c3s_1948_, v_p_1962_);
v___x_1964_ = 0;
v___x_1965_ = 0;
lean_inc_ref(v___x_1963_);
lean_inc_ref(v_lctx_1959_);
v___x_1966_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1959_, v_uniq_1961_, v_name_1960_, v___x_1963_, v___x_1964_, v___x_1965_);
v___x_1967_ = l_Lean_Expr_fvar___override(v_uniq_1961_);
v___x_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1963_);
v___x_1969_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_stx_1947_, v___x_1966_, v___x_1967_, v___x_1968_, v_isBinder_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_1969_;
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_hyp_1949_);
lean_dec_ref(v_00_u03c3s_1948_);
lean_dec(v_stx_1947_);
v_a_1970_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1957_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1957_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed(lean_object* v_stx_1978_, lean_object* v_00_u03c3s_1979_, lean_object* v_hyp_1980_, lean_object* v_isBinder_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
uint8_t v_isBinder_boxed_1987_; lean_object* v_res_1988_; 
v_isBinder_boxed_1987_ = lean_unbox(v_isBinder_1981_);
v_res_1988_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_stx_1978_, v_00_u03c3s_1979_, v_hyp_1980_, v_isBinder_boxed_1987_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
return v_res_1988_;
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
