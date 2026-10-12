// Lean compiler output
// Module: Lean.Elab.Tactic.Guard
// Imports: public import Init.Guard public import Lean.Elab.Command public import Lean.Elab.Tactic.Conv.Basic
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colon"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 254, 84, 58, 178, 14, 199, 231)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "colonR"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(51, 135, 112, 228, 153, 36, 76, 163)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "colonD"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(239, 18, 30, 158, 90, 1, 40, 60)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "colonS"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value),LEAN_SCALAR_PTR_LITERAL(193, 176, 35, 153, 39, 172, 5, 224)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "colonA"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value),LEAN_SCALAR_PTR_LITERAL(174, 248, 67, 94, 236, 67, 221, 38)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "colonEq"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 195, 203, 230, 89, 211, 239, 47)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "colonEqR"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(39, 95, 109, 198, 172, 241, 26, 63)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "colonEqD"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 97, 32, 12, 243, 89, 105, 131)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "colonEqS"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(85, 174, 78, 53, 52, 85, 48, 251)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "colonEqA"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value),LEAN_SCALAR_PTR_LITERAL(64, 40, 146, 207, 24, 72, 136, 5)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "equal"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 80, 62, 47, 176, 56, 79, 244)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "equalR"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 8, 237, 98, 162, 170, 4, 237)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "equalD"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 0, 219, 113, 131, 147, 252, 124)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "equalS"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(136, 190, 244, 204, 191, 159, 89, 191)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "equalA"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value),LEAN_SCALAR_PTR_LITERAL(103, 173, 120, 27, 241, 99, 125, 120)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "syntactically equal to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "definitionally equal (unfolding all constants) to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "definitionally equal to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "definitionally equal (unfolding reducible constants) to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "definitionally equal (unfolding instance_reducible) to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "definitionally equal (not unfolding any constants) to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "definitionally equal (unfolding instance_reducible and implicit_reducible) to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "alpha-equivalent to"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Failed: `"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` is not "};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "guardExpr"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(81, 0, 57, 230, 6, 90, 102, 33)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "guardExprConv"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(35, 204, 249, 180, 228, 44, 37, 243)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "GuardExpr"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalGuardExpr"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(62, 100, 183, 29, 46, 223, 208, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(75) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(82) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(75) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(75) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "evalGuardExprConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 108, 184, 11, 60, 12, 65, 40)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(86) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(86) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(86) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(86) << 1) | 1)),((lean_object*)(((size_t)(21) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(21) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "The main goal is"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "\nbut was expected to be"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "guardTarget"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 4, 80, 225, 8, 32, 178, 134)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "guardTargetConv"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 167, 126, 167, 155, 13, 186, 15)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Conv_getLhs___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_getMainTarget___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalGuardTarget"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 153, 63, 243, 233, 124, 63, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(99) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(89) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "evalGuardTargetConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 201, 37, 165, 174, 253, 123, 45)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(103) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(103) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(103) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(103) << 1) | 1)),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a let binding"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` is a let binding"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Hypothesis `"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` has value"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "\nbut was expected to have value"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "\nbut was expected to have type"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` not found"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "guardHyp"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 79, 231, 38, 72, 47, 167, 177)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "guardHypConv"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(249, 4, 67, 240, 71, 133, 21, 138)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalGuardHyp"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 159, 154, 219, 163, 190, 113, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(106) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(106) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(106) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalGuardHypConv"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 54, 125, 106, 129, 114, 238, 3)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(133) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(133) << 1) | 1)),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value),((lean_object*)(((size_t)(45) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(133) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(133) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "guardExprCmd"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 243, 228, 205, 228, 23, 93, 39)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalGuardExprCmd"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 94, 35, 33, 234, 204, 197, 194)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(136) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(143) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(136) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(136) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Expression"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "\ndid not evaluate to `true`"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "guardCmd"};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 150, 251, 111, 125, 167, 179, 116)}};
static const lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalGuardCmd"};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 92, 80, 228, 105, 220, 20, 129)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 78, 68, 148, 10, 117, 178, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(146) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(158) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(146) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(146) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 1)
{
uint8_t v_red_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_red_7_ = lean_ctor_get_uint8(v_t_5_, 0);
v___x_8_ = lean_box(v_red_7_);
v___x_9_ = lean_apply_1(v_k_6_, v___x_8_);
return v___x_9_;
}
else
{
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg___boxed(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_10_, v_k_11_);
lean_dec(v_t_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_t_21_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(lean_object* v_t_25_, lean_object* v_syntactic_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_25_, v_syntactic_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg___boxed(lean_object* v_t_28_, lean_object* v_syntactic_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(v_t_28_, v_syntactic_29_);
lean_dec(v_t_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_syntactic_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_32_, v_syntactic_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_syntactic_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(v_motive_36_, v_t_37_, v_h_38_, v_syntactic_39_);
lean_dec(v_t_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(lean_object* v_t_41_, lean_object* v_defEq_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_41_, v_defEq_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg___boxed(lean_object* v_t_44_, lean_object* v_defEq_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(v_t_44_, v_defEq_45_);
lean_dec(v_t_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_defEq_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_48_, v_defEq_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___boxed(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_defEq_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(v_motive_52_, v_t_53_, v_h_54_, v_defEq_55_);
lean_dec(v_t_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(lean_object* v_t_57_, lean_object* v_alphaEq_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_57_, v_alphaEq_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg___boxed(lean_object* v_t_60_, lean_object* v_alphaEq_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(v_t_60_, v_alphaEq_61_);
lean_dec(v_t_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_alphaEq_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_64_, v_alphaEq_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_alphaEq_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(v_motive_68_, v_t_69_, v_h_70_, v_alphaEq_71_);
lean_dec(v_t_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3));
lean_inc(v_x_112_);
v___x_114_ = l_Lean_Syntax_isOfKind(v_x_112_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec(v_x_112_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_112_, v___x_116_);
lean_dec(v_x_112_);
v___x_118_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5));
lean_inc(v___x_117_);
v___x_119_ = l_Lean_Syntax_isOfKind(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7));
lean_inc(v___x_117_);
v___x_121_ = l_Lean_Syntax_isOfKind(v___x_117_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9));
lean_inc(v___x_117_);
v___x_123_ = l_Lean_Syntax_isOfKind(v___x_117_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11));
v___x_125_ = l_Lean_Syntax_isOfKind(v___x_117_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12));
return v___x_127_;
}
}
else
{
lean_object* v___x_128_; 
lean_dec(v___x_117_);
v___x_128_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13));
return v___x_128_;
}
}
else
{
lean_object* v___x_129_; 
lean_dec(v___x_117_);
v___x_129_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15));
return v___x_129_;
}
}
else
{
lean_object* v___x_130_; 
lean_dec(v___x_117_);
v___x_130_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17));
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(lean_object* v_x_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1));
lean_inc(v_x_156_);
v___x_158_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
lean_dec(v_x_156_);
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = l_Lean_Syntax_getArg(v_x_156_, v___x_160_);
lean_dec(v_x_156_);
v___x_162_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3));
lean_inc(v___x_161_);
v___x_163_ = l_Lean_Syntax_isOfKind(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5));
lean_inc(v___x_161_);
v___x_165_ = l_Lean_Syntax_isOfKind(v___x_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7));
lean_inc(v___x_161_);
v___x_167_ = l_Lean_Syntax_isOfKind(v___x_161_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9));
v___x_169_ = l_Lean_Syntax_isOfKind(v___x_161_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12));
return v___x_171_;
}
}
else
{
lean_object* v___x_172_; 
lean_dec(v___x_161_);
v___x_172_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13));
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; 
lean_dec(v___x_161_);
v___x_173_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15));
return v___x_173_;
}
}
else
{
lean_object* v___x_174_; 
lean_dec(v___x_161_);
v___x_174_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17));
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_x_200_);
v___x_202_ = l_Lean_Syntax_isOfKind(v_x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec(v_x_200_);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Lean_Syntax_getArg(v_x_200_, v___x_204_);
lean_dec(v_x_200_);
v___x_206_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3));
lean_inc(v___x_205_);
v___x_207_ = l_Lean_Syntax_isOfKind(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5));
lean_inc(v___x_205_);
v___x_209_ = l_Lean_Syntax_isOfKind(v___x_205_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7));
lean_inc(v___x_205_);
v___x_211_ = l_Lean_Syntax_isOfKind(v___x_205_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9));
v___x_213_ = l_Lean_Syntax_isOfKind(v___x_205_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12));
return v___x_215_;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v___x_205_);
v___x_216_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13));
return v___x_216_;
}
}
else
{
lean_object* v___x_217_; 
lean_dec(v___x_205_);
v___x_217_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15));
return v___x_217_;
}
}
else
{
lean_object* v___x_218_; 
lean_dec(v___x_205_);
v___x_218_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17));
return v___x_218_;
}
}
}
}
lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(lean_object* v_x_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_saveState___redArg(v___y_221_, v___y_223_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v_r_227_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
lean_inc(v___y_223_);
lean_inc_ref(v___y_222_);
lean_inc(v___y_221_);
lean_inc_ref(v___y_220_);
v_r_227_ = lean_apply_5(v_x_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, lean_box(0));
if (lean_obj_tag(v_r_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; 
v_a_228_ = lean_ctor_get(v_r_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v_r_227_, 1);
v___x_229_ = l_Lean_Meta_SavedState_restore___redArg(v_a_226_, v___y_221_, v___y_223_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_236_ == 0)
{
lean_object* v_unused_237_; 
v_unused_237_ = lean_ctor_get(v___x_229_, 0);
lean_dec(v_unused_237_);
v___x_231_ = v___x_229_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_dec(v___x_229_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v_a_228_);
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_228_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_a_228_);
v_a_238_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_229_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_229_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v_r_227_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v_r_227_, 1);
v___x_247_ = l_Lean_Meta_SavedState_restore___redArg(v_a_226_, v___y_221_, v___y_223_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v___x_247_, 0);
lean_dec(v_unused_255_);
v___x_249_ = v___x_247_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_dec(v___x_247_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 1);
lean_ctor_set(v___x_249_, 0, v_a_246_);
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_246_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_246_);
v_a_256_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_247_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_247_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref(v_x_219_);
v_a_264_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_225_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_225_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_219_ = stack[0].m_obj;
lean_object* v___y_220_ = stack[1].m_obj;
lean_object* v___y_221_ = stack[2].m_obj;
lean_object* v___y_222_ = stack[3].m_obj;
lean_object* v___y_223_ = stack[4].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg___boxed(lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(lean_object* v_00_u03b1_280_, lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
return v___x_287_;
}
}
LEAN_EXPORT void l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_281_ = stack[1].m_obj;
lean_object* v___y_282_ = stack[2].m_obj;
lean_object* v___y_283_ = stack[3].m_obj;
lean_object* v___y_284_ = stack[4].m_obj;
lean_object* v___y_285_ = stack[5].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(lean_box(0), v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___boxed(lean_object* v_00_u03b1_289_, lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(v_00_u03b1_289_, v_x_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(uint8_t v_red_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___y_306_; lean_object* v___x_323_; uint8_t v_transparency_324_; uint8_t v___x_325_; 
v___x_323_ = l_Lean_Meta_Context_config(v___y_300_);
v_transparency_324_ = lean_ctor_get_uint8(v___x_323_, 9);
lean_dec_ref(v___x_323_);
v___x_325_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_324_, v_red_297_);
if (v___x_325_ == 0)
{
lean_object* v_keyedConfig_326_; uint8_t v_trackZetaDelta_327_; lean_object* v_zetaDeltaSet_328_; lean_object* v_lctx_329_; lean_object* v_localInstances_330_; lean_object* v_defEqCtx_x3f_331_; lean_object* v_synthPendingDepth_332_; lean_object* v_customCanUnfoldPredicate_x3f_333_; uint8_t v_univApprox_334_; uint8_t v_inTypeClassResolution_335_; uint8_t v_cacheInferType_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_345_; 
v_keyedConfig_326_ = lean_ctor_get(v___y_300_, 0);
v_trackZetaDelta_327_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7);
v_zetaDeltaSet_328_ = lean_ctor_get(v___y_300_, 1);
v_lctx_329_ = lean_ctor_get(v___y_300_, 2);
v_localInstances_330_ = lean_ctor_get(v___y_300_, 3);
v_defEqCtx_x3f_331_ = lean_ctor_get(v___y_300_, 4);
v_synthPendingDepth_332_ = lean_ctor_get(v___y_300_, 5);
v_customCanUnfoldPredicate_x3f_333_ = lean_ctor_get(v___y_300_, 6);
v_univApprox_334_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_335_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7 + 2);
v_cacheInferType_336_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7 + 3);
v_isSharedCheck_345_ = !lean_is_exclusive(v___y_300_);
if (v_isSharedCheck_345_ == 0)
{
v___x_338_ = v___y_300_;
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_333_);
lean_inc(v_synthPendingDepth_332_);
lean_inc(v_defEqCtx_x3f_331_);
lean_inc(v_localInstances_330_);
lean_inc(v_lctx_329_);
lean_inc(v_zetaDeltaSet_328_);
lean_inc(v_keyedConfig_326_);
lean_dec(v___y_300_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_345_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = l_Lean_Meta_ConfigWithKey_setTransparency(v_red_297_, v_keyedConfig_326_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_zetaDeltaSet_328_);
lean_ctor_set(v_reuseFailAlloc_344_, 2, v_lctx_329_);
lean_ctor_set(v_reuseFailAlloc_344_, 3, v_localInstances_330_);
lean_ctor_set(v_reuseFailAlloc_344_, 4, v_defEqCtx_x3f_331_);
lean_ctor_set(v_reuseFailAlloc_344_, 5, v_synthPendingDepth_332_);
lean_ctor_set(v_reuseFailAlloc_344_, 6, v_customCanUnfoldPredicate_x3f_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_344_, sizeof(void*)*7, v_trackZetaDelta_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_344_, sizeof(void*)*7 + 1, v_univApprox_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_344_, sizeof(void*)*7 + 2, v_inTypeClassResolution_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_344_, sizeof(void*)*7 + 3, v_cacheInferType_336_);
v___x_342_ = v_reuseFailAlloc_344_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_isExprDefEqGuarded(v_a_298_, v_b_299_, v___x_342_, v___y_301_, v___y_302_, v___y_303_);
lean_dec_ref(v___x_342_);
v___y_306_ = v___x_343_;
goto v___jp_305_;
}
}
}
else
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_isExprDefEqGuarded(v_a_298_, v_b_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec_ref(v___y_300_);
v___y_306_ = v___x_346_;
goto v___jp_305_;
}
v___jp_305_:
{
if (lean_obj_tag(v___y_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
v_a_307_ = lean_ctor_get(v___y_306_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___y_306_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___y_306_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___y_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v___y_306_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___y_306_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___y_306_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___y_306_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_red_297_ = stack[0].m_num;
lean_object* v_a_298_ = stack[1].m_obj;
lean_object* v_b_299_ = stack[2].m_obj;
lean_object* v___y_300_ = stack[3].m_obj;
lean_object* v___y_301_ = stack[4].m_obj;
lean_object* v___y_302_ = stack[5].m_obj;
lean_object* v___y_303_ = stack[6].m_obj;
lean_object* v_res_347_;
v_res_347_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(v_red_297_, v_a_298_, v_b_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(lean_object* v_red_348_, lean_object* v_a_349_, lean_object* v_b_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
uint8_t v_red_1691__boxed_356_; lean_object* v_res_357_; 
v_red_1691__boxed_356_ = lean_unbox(v_red_348_);
v_res_357_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(v_red_1691__boxed_356_, v_a_349_, v_b_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
return v_res_357_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object* v_a_358_, lean_object* v_b_359_, lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
switch(lean_obj_tag(v_x_360_))
{
case 0:
{
lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = l_Lean_Expr_consumeMData(v_a_358_);
lean_dec_ref(v_a_358_);
v___x_367_ = l_Lean_Expr_consumeMData(v_b_359_);
lean_dec_ref(v_b_359_);
v___x_368_ = lean_expr_eqv(v___x_366_, v___x_367_);
lean_dec_ref(v___x_367_);
lean_dec_ref(v___x_366_);
v___x_369_ = lean_box(v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
case 1:
{
uint8_t v_red_371_; lean_object* v___x_372_; lean_object* v___f_373_; lean_object* v___x_374_; 
v_red_371_ = lean_ctor_get_uint8(v_x_360_, 0);
v___x_372_ = lean_box(v_red_371_);
v___f_373_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_373_, 0, v___x_372_);
lean_closure_set(v___f_373_, 1, v_a_358_);
lean_closure_set(v___f_373_, 2, v_b_359_);
v___x_374_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v___f_373_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
return v___x_374_;
}
default: 
{
uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = lean_expr_eqv(v_a_358_, v_b_359_);
lean_dec_ref(v_b_359_);
lean_dec_ref(v_a_358_);
v___x_376_ = lean_box(v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_358_ = stack[0].m_obj;
lean_object* v_b_359_ = stack[1].m_obj;
lean_object* v_x_360_ = stack[2].m_obj;
lean_object* v_a_361_ = stack[3].m_obj;
lean_object* v_a_362_ = stack[4].m_obj;
lean_object* v_a_363_ = stack[5].m_obj;
lean_object* v_a_364_ = stack[6].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_358_, v_b_359_, v_x_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(lean_object* v_a_379_, lean_object* v_b_380_, lean_object* v_x_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_379_, v_b_380_, v_x_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_x_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(lean_object* v_x_396_){
_start:
{
switch(lean_obj_tag(v_x_396_))
{
case 0:
{
lean_object* v___x_397_; 
v___x_397_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0));
return v___x_397_;
}
case 1:
{
uint8_t v_red_398_; 
v_red_398_ = lean_ctor_get_uint8(v_x_396_, 0);
switch(v_red_398_)
{
case 0:
{
lean_object* v___x_399_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1));
return v___x_399_;
}
case 1:
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2));
return v___x_400_;
}
case 2:
{
lean_object* v___x_401_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3));
return v___x_401_;
}
case 3:
{
lean_object* v___x_402_; 
v___x_402_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4));
return v___x_402_;
}
case 4:
{
lean_object* v___x_403_; 
v___x_403_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5));
return v___x_403_;
}
default: 
{
lean_object* v___x_404_; 
v___x_404_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6));
return v___x_404_;
}
}
}
default: 
{
lean_object* v___x_405_; 
v___x_405_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__7));
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___boxed(lean_object* v_x_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_x_406_);
lean_dec(v_x_406_);
return v_res_407_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(lean_object* v_e_408_, lean_object* v___y_409_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = l_Lean_Expr_hasMVar(v_e_408_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_e_408_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v_mctx_414_; lean_object* v___x_415_; lean_object* v_fst_416_; lean_object* v_snd_417_; lean_object* v___x_418_; lean_object* v_cache_419_; lean_object* v_zetaDeltaFVarIds_420_; lean_object* v_postponed_421_; lean_object* v_diag_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_431_; 
v___x_413_ = lean_st_ref_get(v___y_409_);
v_mctx_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_ref(v_mctx_414_);
lean_dec(v___x_413_);
v___x_415_ = l_Lean_instantiateMVarsCore(v_mctx_414_, v_e_408_);
v_fst_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_fst_416_);
v_snd_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_snd_417_);
lean_dec_ref(v___x_415_);
v___x_418_ = lean_st_ref_take(v___y_409_);
v_cache_419_ = lean_ctor_get(v___x_418_, 1);
v_zetaDeltaFVarIds_420_ = lean_ctor_get(v___x_418_, 2);
v_postponed_421_ = lean_ctor_get(v___x_418_, 3);
v_diag_422_ = lean_ctor_get(v___x_418_, 4);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v___x_418_, 0);
lean_dec(v_unused_432_);
v___x_424_ = v___x_418_;
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_diag_422_);
lean_inc(v_postponed_421_);
lean_inc(v_zetaDeltaFVarIds_420_);
lean_inc(v_cache_419_);
lean_dec(v___x_418_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_431_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v_snd_417_);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_snd_417_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_cache_419_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v_zetaDeltaFVarIds_420_);
lean_ctor_set(v_reuseFailAlloc_430_, 3, v_postponed_421_);
lean_ctor_set(v_reuseFailAlloc_430_, 4, v_diag_422_);
v___x_427_ = v_reuseFailAlloc_430_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_st_ref_put(v___y_409_, v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_fst_416_);
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_408_ = stack[0].m_obj;
lean_object* v___y_409_ = stack[1].m_obj;
lean_object* v_res_433_;
v_res_433_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_408_, v___y_409_);
stack->m_obj
 = v_res_433_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(lean_object* v_e_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_434_, v___y_435_);
lean_dec(v___y_435_);
return v_res_437_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(lean_object* v_e_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_438_, v___y_442_);
return v___x_446_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_438_ = stack[0].m_obj;
lean_object* v___y_439_ = stack[1].m_obj;
lean_object* v___y_440_ = stack[2].m_obj;
lean_object* v___y_441_ = stack[3].m_obj;
lean_object* v___y_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v___y_444_ = stack[6].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(v_e_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(lean_object* v_e_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(v_e_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_456_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(lean_object* v_a_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
return v___x_465_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_457_ = stack[0].m_obj;
lean_object* v___y_458_ = stack[1].m_obj;
lean_object* v___y_459_ = stack[2].m_obj;
lean_object* v___y_460_ = stack[3].m_obj;
lean_object* v___y_461_ = stack[4].m_obj;
lean_object* v___y_462_ = stack[5].m_obj;
lean_object* v___y_463_ = stack[6].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(v_a_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg___boxed(lean_object* v_a_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(v_a_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v_res_475_;
}
}
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(lean_object* v_00_u03b1_476_, lean_object* v_a_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
return v___x_485_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_477_ = stack[1].m_obj;
lean_object* v___y_478_ = stack[2].m_obj;
lean_object* v___y_479_ = stack[3].m_obj;
lean_object* v___y_480_ = stack[4].m_obj;
lean_object* v___y_481_ = stack[5].m_obj;
lean_object* v___y_482_ = stack[6].m_obj;
lean_object* v___y_483_ = stack[7].m_obj;
lean_object* v_res_486_;
v_res_486_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(lean_box(0), v_a_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
stack->m_obj
 = v_res_486_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___boxed(lean_object* v_00_u03b1_487_, lean_object* v_a_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(v_00_u03b1_487_, v_a_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
return v_res_496_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(lean_object* v_a_497_, lean_object* v___x_498_, uint8_t v___x_499_, lean_object* v_b_500_, lean_object* v_mk_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
lean_inc(v___x_498_);
v___x_509_ = l_Lean_Elab_Term_elabTerm(v_a_497_, v___x_498_, v___x_499_, v___x_499_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Elab_Term_elabTerm(v_b_500_, v___x_498_, v___x_499_, v___x_499_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
lean_inc(v___y_507_);
lean_inc_ref(v___y_506_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v_a_510_);
v___x_513_ = lean_infer_type(v_a_510_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
lean_inc(v___y_507_);
lean_inc_ref(v___y_506_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v_a_512_);
v___x_515_ = lean_infer_type(v_a_512_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_517_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v___x_517_ = l_Lean_Meta_isExprDefEqGuarded(v_a_514_, v_a_516_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_517_) == 0)
{
uint8_t v___x_518_; lean_object* v___x_519_; 
lean_dec_ref_known(v___x_517_, 1);
v___x_518_ = 0;
v___x_519_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_518_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v_a_523_; lean_object* v___x_524_; 
lean_dec_ref_known(v___x_519_, 1);
v___x_520_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_510_, v___y_505_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v___x_522_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_512_, v___y_505_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_521_, v_a_523_, v_mk_501_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v___x_524_;
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_a_512_);
lean_dec(v_a_510_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
v_a_525_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_519_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_519_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_dec(v_a_512_);
lean_dec(v_a_510_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v___x_517_;
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_514_);
lean_dec(v_a_512_);
lean_dec(v_a_510_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
v_a_533_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_515_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_515_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_512_);
lean_dec(v_a_510_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
v_a_541_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_513_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_513_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
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
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_a_510_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
v_a_549_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_511_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_511_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v_b_500_);
lean_dec(v___x_498_);
v_a_557_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_509_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_509_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_497_ = stack[0].m_obj;
lean_object* v___x_498_ = stack[1].m_obj;
uint8_t v___x_499_ = stack[2].m_num;
lean_object* v_b_500_ = stack[3].m_obj;
lean_object* v_mk_501_ = stack[4].m_obj;
lean_object* v___y_502_ = stack[5].m_obj;
lean_object* v___y_503_ = stack[6].m_obj;
lean_object* v___y_504_ = stack[7].m_obj;
lean_object* v___y_505_ = stack[8].m_obj;
lean_object* v___y_506_ = stack[9].m_obj;
lean_object* v___y_507_ = stack[10].m_obj;
lean_object* v_res_565_;
v_res_565_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(v_a_497_, v___x_498_, v___x_499_, v_b_500_, v_mk_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
stack->m_obj
 = v_res_565_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed(lean_object* v_a_566_, lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v_b_569_, lean_object* v_mk_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
uint8_t v___x_1884__boxed_578_; lean_object* v_res_579_; 
v___x_1884__boxed_578_ = lean_unbox(v___x_568_);
v_res_579_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(v_a_566_, v___x_567_, v___x_1884__boxed_578_, v_b_569_, v_mk_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v_mk_570_);
return v_res_579_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object* v_mk_580_, lean_object* v_a_581_, lean_object* v_b_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_590_; uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___f_593_; lean_object* v___x_594_; 
v___x_590_ = lean_box(0);
v___x_591_ = 1;
v___x_592_ = lean_box(v___x_591_);
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed), 12, 5);
lean_closure_set(v___f_593_, 0, v_a_581_);
lean_closure_set(v___f_593_, 1, v___x_590_);
lean_closure_set(v___f_593_, 2, v___x_592_);
lean_closure_set(v___f_593_, 3, v_b_582_);
lean_closure_set(v___f_593_, 4, v_mk_580_);
v___x_594_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_593_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
return v___x_594_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_mk_580_ = stack[0].m_obj;
lean_object* v_a_581_ = stack[1].m_obj;
lean_object* v_b_582_ = stack[2].m_obj;
lean_object* v_a_583_ = stack[3].m_obj;
lean_object* v_a_584_ = stack[4].m_obj;
lean_object* v_a_585_ = stack[5].m_obj;
lean_object* v_a_586_ = stack[6].m_obj;
lean_object* v_a_587_ = stack[7].m_obj;
lean_object* v_a_588_ = stack[8].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_mk_580_, v_a_581_, v_b_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___boxed(lean_object* v_mk_596_, lean_object* v_a_597_, lean_object* v_b_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_mk_596_, v_a_597_, v_b_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
lean_dec(v_a_600_);
lean_dec_ref(v_a_599_);
return v_res_606_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_box(0);
v___x_608_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
return v___x_609_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_613_;
v_res_613_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___boxed(lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v_res_615_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(lean_object* v_00_u03b1_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_626_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_617_ = stack[1].m_obj;
lean_object* v___y_618_ = stack[2].m_obj;
lean_object* v___y_619_ = stack[3].m_obj;
lean_object* v___y_620_ = stack[4].m_obj;
lean_object* v___y_621_ = stack[5].m_obj;
lean_object* v___y_622_ = stack[6].m_obj;
lean_object* v___y_623_ = stack[7].m_obj;
lean_object* v___y_624_ = stack[8].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(lean_box(0), v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___boxed(lean_object* v_00_u03b1_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(v_00_u03b1_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_638_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(lean_object* v_msgData_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_env_646_; uint8_t v___x_647_; lean_object* v_env_648_; lean_object* v___x_649_; lean_object* v_toCold_650_; lean_object* v_mctx_651_; lean_object* v_lctx_652_; lean_object* v_options_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_645_ = lean_st_ref_get(v___y_643_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc_ref(v_env_646_);
lean_dec(v___x_645_);
v___x_647_ = 0;
v_env_648_ = l_Lean_Environment_setRecordingDeps(v_env_646_, v___x_647_);
v___x_649_ = lean_st_ref_get(v___y_641_);
v_toCold_650_ = lean_ctor_get(v___y_642_, 0);
v_mctx_651_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_mctx_651_);
lean_dec(v___x_649_);
v_lctx_652_ = lean_ctor_get(v___y_640_, 2);
v_options_653_ = lean_ctor_get(v_toCold_650_, 2);
lean_inc_ref(v_options_653_);
lean_inc_ref(v_lctx_652_);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v_env_648_);
lean_ctor_set(v___x_654_, 1, v_mctx_651_);
lean_ctor_set(v___x_654_, 2, v_lctx_652_);
lean_ctor_set(v___x_654_, 3, v_options_653_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_msgData_639_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_639_ = stack[0].m_obj;
lean_object* v___y_640_ = stack[1].m_obj;
lean_object* v___y_641_ = stack[2].m_obj;
lean_object* v___y_642_ = stack[3].m_obj;
lean_object* v___y_643_ = stack[4].m_obj;
lean_object* v_res_657_;
v_res_657_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msgData_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1___boxed(lean_object* v_msgData_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msgData_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_664_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_ref_671_; lean_object* v___x_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_681_; 
v_ref_671_ = lean_ctor_get(v___y_668_, 2);
v___x_672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_681_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_681_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_inc(v_ref_671_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_ref_671_);
lean_ctor_set(v___x_677_, 1, v_a_673_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 1);
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_665_ = stack[0].m_obj;
lean_object* v___y_666_ = stack[1].m_obj;
lean_object* v___y_667_ = stack[2].m_obj;
lean_object* v___y_668_ = stack[3].m_obj;
lean_object* v___y_669_ = stack[4].m_obj;
lean_object* v_res_682_;
v_res_682_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg___boxed(lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v_msg_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v_res_689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4));
v___x_698_ = l_Lean_stringToMessageData(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(lean_object* v___x_702_, lean_object* v_r_703_, lean_object* v_p_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
if (lean_obj_tag(v___x_702_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_715_; 
v_val_714_ = lean_ctor_get(v___x_702_, 0);
lean_inc_n(v_val_714_, 2);
lean_dec_ref_known(v___x_702_, 1);
lean_inc(v_p_704_);
lean_inc(v_r_703_);
v___x_715_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_val_714_, v_r_703_, v_p_704_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_740_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_740_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_740_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_740_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
uint8_t v___x_720_; 
v___x_720_ = lean_unbox(v_a_716_);
lean_dec(v_a_716_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
lean_del_object(v___x_718_);
v___x_721_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1);
v___x_722_ = l_Lean_MessageData_ofSyntax(v_r_703_);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_714_);
lean_dec(v_val_714_);
v___x_727_ = l_Lean_stringToMessageData(v___x_726_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_725_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5);
v___x_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Lean_MessageData_ofSyntax(v_p_704_);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_734_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_738_; 
lean_dec(v_val_714_);
lean_dec(v_p_704_);
lean_dec(v_r_703_);
v___x_736_ = lean_box(0);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_736_);
v___x_738_ = v___x_718_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_736_);
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
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_val_714_);
lean_dec(v_p_704_);
lean_dec(v_r_703_);
v_a_741_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_715_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_715_);
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
lean_object* v___x_749_; 
lean_dec(v_p_704_);
lean_dec(v_r_703_);
lean_dec(v___x_702_);
v___x_749_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_749_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_702_ = stack[0].m_obj;
lean_object* v_r_703_ = stack[1].m_obj;
lean_object* v_p_704_ = stack[2].m_obj;
lean_object* v___y_705_ = stack[3].m_obj;
lean_object* v___y_706_ = stack[4].m_obj;
lean_object* v___y_707_ = stack[5].m_obj;
lean_object* v___y_708_ = stack[6].m_obj;
lean_object* v___y_709_ = stack[7].m_obj;
lean_object* v___y_710_ = stack[8].m_obj;
lean_object* v___y_711_ = stack[9].m_obj;
lean_object* v___y_712_ = stack[10].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(v___x_702_, v_r_703_, v_p_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed(lean_object* v___x_751_, lean_object* v_r_752_, lean_object* v_p_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(v___x_751_, v_r_752_, v_p_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_763_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object* v_x_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2));
lean_inc(v_x_777_);
v___x_788_ = l_Lean_Syntax_isOfKind(v_x_777_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4));
lean_inc(v_x_777_);
v___x_790_ = l_Lean_Syntax_isOfKind(v_x_777_, v___x_789_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v_x_777_);
v___x_791_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_791_;
}
else
{
lean_object* v___x_792_; lean_object* v_r_793_; lean_object* v___x_794_; lean_object* v_eq_795_; 
v___x_792_ = lean_unsigned_to_nat(1u);
v_r_793_ = l_Lean_Syntax_getArg(v_x_777_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(2u);
v_eq_795_ = l_Lean_Syntax_getArg(v_x_777_, v___x_794_);
if (v___x_788_ == 0)
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_795_);
v___x_803_ = l_Lean_Syntax_isOfKind(v_eq_795_, v___x_802_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; 
lean_dec(v_eq_795_);
lean_dec(v_r_793_);
lean_dec(v_x_777_);
v___x_804_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_804_;
}
else
{
goto v___jp_796_;
}
}
else
{
goto v___jp_796_;
}
v___jp_796_:
{
lean_object* v___x_797_; lean_object* v_p_798_; lean_object* v___x_799_; lean_object* v___y_800_; lean_object* v___x_801_; 
v___x_797_ = lean_unsigned_to_nat(3u);
v_p_798_ = l_Lean_Syntax_getArg(v_x_777_, v___x_797_);
lean_dec(v_x_777_);
v___x_799_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_795_);
v___y_800_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 12, 3);
lean_closure_set(v___y_800_, 0, v___x_799_);
lean_closure_set(v___y_800_, 1, v_r_793_);
lean_closure_set(v___y_800_, 2, v_p_798_);
v___x_801_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_800_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_801_;
}
}
}
else
{
lean_object* v___x_805_; lean_object* v_eq_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_805_ = lean_unsigned_to_nat(2u);
v_eq_806_ = l_Lean_Syntax_getArg(v_x_777_, v___x_805_);
v___x_807_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_806_);
v___x_808_ = l_Lean_Syntax_isOfKind(v_eq_806_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_eq_806_);
lean_dec(v_x_777_);
v___x_809_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v_r_811_; lean_object* v___x_812_; lean_object* v_p_813_; lean_object* v___x_814_; lean_object* v___y_815_; lean_object* v___x_816_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v_r_811_ = l_Lean_Syntax_getArg(v_x_777_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(3u);
v_p_813_ = l_Lean_Syntax_getArg(v_x_777_, v___x_812_);
lean_dec(v_x_777_);
v___x_814_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_806_);
v___y_815_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 12, 3);
lean_closure_set(v___y_815_, 0, v___x_814_);
lean_closure_set(v___y_815_, 1, v_r_811_);
lean_closure_set(v___y_815_, 2, v_p_813_);
v___x_816_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_815_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_816_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_777_ = stack[0].m_obj;
lean_object* v_a_778_ = stack[1].m_obj;
lean_object* v_a_779_ = stack[2].m_obj;
lean_object* v_a_780_ = stack[3].m_obj;
lean_object* v_a_781_ = stack[4].m_obj;
lean_object* v_a_782_ = stack[5].m_obj;
lean_object* v_a_783_ = stack[6].m_obj;
lean_object* v_a_784_ = stack[7].m_obj;
lean_object* v_a_785_ = stack[8].m_obj;
lean_object* v_res_817_;
v_res_817_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(v_x_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed(lean_object* v_x_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(v_x_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_828_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(lean_object* v_00_u03b1_829_, lean_object* v_msg_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v_msg_830_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
return v___x_840_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_830_ = stack[1].m_obj;
lean_object* v___y_831_ = stack[2].m_obj;
lean_object* v___y_832_ = stack[3].m_obj;
lean_object* v___y_833_ = stack[4].m_obj;
lean_object* v___y_834_ = stack[5].m_obj;
lean_object* v___y_835_ = stack[6].m_obj;
lean_object* v___y_836_ = stack[7].m_obj;
lean_object* v___y_837_ = stack[8].m_obj;
lean_object* v___y_838_ = stack[9].m_obj;
lean_object* v_res_841_;
v_res_841_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(lean_box(0), v_msg_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___boxed(lean_object* v_00_u03b1_842_, lean_object* v_msg_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(v_00_u03b1_842_, v_msg_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_853_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1(){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_864_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_865_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2));
v___x_866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3));
v___x_867_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed), 10, 0);
v___x_868_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_864_, v___x_865_, v___x_866_, v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_869_;
v_res_869_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___boxed(lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
return v_res_871_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3(){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3));
v___x_899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6));
v___x_900_ = l_Lean_addBuiltinDeclarationRanges(v___x_898_, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_901_;
v_res_901_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___boxed(lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
return v_res_903_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_914_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_904_ = stack[0].m_obj;
lean_object* v_a_905_ = stack[1].m_obj;
lean_object* v_a_906_ = stack[2].m_obj;
lean_object* v_a_907_ = stack[3].m_obj;
lean_object* v_a_908_ = stack[4].m_obj;
lean_object* v_a_909_ = stack[5].m_obj;
lean_object* v_a_910_ = stack[6].m_obj;
lean_object* v_a_911_ = stack[7].m_obj;
lean_object* v_a_912_ = stack[8].m_obj;
lean_object* v_res_915_;
v_res_915_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
stack->m_obj
 = v_res_915_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_926_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1(){
_start:
{
lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed), 10, 0);
v___x_936_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_937_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4));
v___x_938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1));
v___x_939_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_936_, v___x_937_, v___x_938_, v___f_935_);
return v___x_939_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_940_;
v_res_940_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
stack->m_obj
 = v_res_940_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___boxed(lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
return v_res_942_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3(){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1));
v___x_970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6));
v___x_971_ = l_Lean_addBuiltinDeclarationRanges(v___x_969_, v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_972_;
v_res_972_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___boxed(lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
return v_res_974_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(lean_object* v_e_975_, lean_object* v___y_976_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = l_Lean_Expr_hasMVar(v_e_975_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v_e_975_);
return v___x_979_;
}
else
{
lean_object* v___x_980_; lean_object* v_mctx_981_; lean_object* v___x_982_; lean_object* v_fst_983_; lean_object* v_snd_984_; lean_object* v___x_985_; lean_object* v_cache_986_; lean_object* v_zetaDeltaFVarIds_987_; lean_object* v_postponed_988_; lean_object* v_diag_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v___x_980_ = lean_st_ref_get(v___y_976_);
v_mctx_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_ref(v_mctx_981_);
lean_dec(v___x_980_);
v___x_982_ = l_Lean_instantiateMVarsCore(v_mctx_981_, v_e_975_);
v_fst_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_983_);
v_snd_984_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_snd_984_);
lean_dec_ref(v___x_982_);
v___x_985_ = lean_st_ref_take(v___y_976_);
v_cache_986_ = lean_ctor_get(v___x_985_, 1);
v_zetaDeltaFVarIds_987_ = lean_ctor_get(v___x_985_, 2);
v_postponed_988_ = lean_ctor_get(v___x_985_, 3);
v_diag_989_ = lean_ctor_get(v___x_985_, 4);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_999_);
v___x_991_ = v___x_985_;
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_diag_989_);
lean_inc(v_postponed_988_);
lean_inc(v_zetaDeltaFVarIds_987_);
lean_inc(v_cache_986_);
lean_dec(v___x_985_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_snd_984_);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_snd_984_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_cache_986_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_zetaDeltaFVarIds_987_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_postponed_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_diag_989_);
v___x_994_ = v_reuseFailAlloc_997_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_st_ref_put(v___y_976_, v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v_fst_983_);
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_975_ = stack[0].m_obj;
lean_object* v___y_976_ = stack[1].m_obj;
lean_object* v_res_1000_;
v_res_1000_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_975_, v___y_976_);
stack->m_obj
 = v_res_1000_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg___boxed(lean_object* v_e_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_1001_, v___y_1002_);
lean_dec(v___y_1002_);
return v_res_1004_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(lean_object* v_e_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_1005_, v___y_1011_);
return v___x_1015_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1005_ = stack[0].m_obj;
lean_object* v___y_1006_ = stack[1].m_obj;
lean_object* v___y_1007_ = stack[2].m_obj;
lean_object* v___y_1008_ = stack[3].m_obj;
lean_object* v___y_1009_ = stack[4].m_obj;
lean_object* v___y_1010_ = stack[5].m_obj;
lean_object* v___y_1011_ = stack[6].m_obj;
lean_object* v___y_1012_ = stack[7].m_obj;
lean_object* v___y_1013_ = stack[8].m_obj;
lean_object* v_res_1016_;
v_res_1016_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(v_e_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
stack->m_obj
 = v_res_1016_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___boxed(lean_object* v_e_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(v_e_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1027_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(lean_object* v_getTgt_1034_, lean_object* v_r_1035_, lean_object* v_eq_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1046_ = lean_apply_9(v_getTgt_1034_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, lean_box(0));
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1107_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_a_1047_, v___y_1042_);
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1107_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1107_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; 
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
lean_inc(v___y_1042_);
lean_inc_ref(v___y_1041_);
lean_inc(v_a_1049_);
v___x_1053_ = lean_infer_type(v_a_1049_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 0, v_a_1054_);
v___x_1056_ = v___x_1051_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1054_);
v___x_1056_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
uint8_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = 0;
v___x_1058_ = l_Lean_Elab_Tactic_elabTerm(v_r_1035_, v___x_1056_, v___x_1057_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_1036_);
if (lean_obj_tag(v___x_1060_) == 1)
{
lean_object* v_val_1061_; lean_object* v___x_1062_; 
v_val_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v___x_1060_, 1);
lean_inc(v_a_1049_);
lean_inc(v_a_1059_);
v___x_1062_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1059_, v_a_1049_, v_val_1061_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v_val_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1080_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1080_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1080_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_unbox(v_a_1063_);
lean_dec(v_a_1063_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_del_object(v___x_1065_);
v___x_1068_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1);
v___x_1069_ = l_Lean_indentExpr(v_a_1049_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_indentExpr(v_a_1059_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1074_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec(v_a_1059_);
lean_dec(v_a_1049_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
v___x_1076_ = lean_box(0);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1076_);
v___x_1078_ = v___x_1065_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_a_1059_);
lean_dec(v_a_1049_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
v_a_1081_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1062_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1062_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
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
else
{
lean_object* v___x_1089_; 
lean_dec(v___x_1060_);
lean_dec(v_a_1059_);
lean_dec(v_a_1049_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
v___x_1089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1089_;
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1049_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v_eq_1036_);
v_a_1090_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1058_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1058_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_del_object(v___x_1051_);
lean_dec(v_a_1049_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v_eq_1036_);
lean_dec(v_r_1035_);
v_a_1099_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1053_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1053_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v_eq_1036_);
lean_dec(v_r_1035_);
v_a_1108_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1046_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1046_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_getTgt_1034_ = stack[0].m_obj;
lean_object* v_r_1035_ = stack[1].m_obj;
lean_object* v_eq_1036_ = stack[2].m_obj;
lean_object* v___y_1037_ = stack[3].m_obj;
lean_object* v___y_1038_ = stack[4].m_obj;
lean_object* v___y_1039_ = stack[5].m_obj;
lean_object* v___y_1040_ = stack[6].m_obj;
lean_object* v___y_1041_ = stack[7].m_obj;
lean_object* v___y_1042_ = stack[8].m_obj;
lean_object* v___y_1043_ = stack[9].m_obj;
lean_object* v___y_1044_ = stack[10].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(v_getTgt_1034_, v_r_1035_, v_eq_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed(lean_object* v_getTgt_1117_, lean_object* v_r_1118_, lean_object* v_eq_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(v_getTgt_1117_, v_r_1118_, v_eq_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v_res_1129_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object* v_x_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_eq_1155_; lean_object* v_r_1156_; lean_object* v_getTgt_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1));
lean_inc(v_x_1144_);
v___x_1169_ = l_Lean_Syntax_isOfKind(v_x_1144_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3));
lean_inc(v_x_1144_);
v___x_1171_ = l_Lean_Syntax_isOfKind(v_x_1144_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_dec(v_x_1144_);
v___x_1172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; lean_object* v_eq_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
v_eq_1174_ = l_Lean_Syntax_getArg(v_x_1144_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(2u);
v___x_1176_ = l_Lean_Syntax_getArg(v_x_1144_, v___x_1175_);
lean_dec(v_x_1144_);
v___x_1177_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4));
v_eq_1155_ = v_eq_1174_;
v_r_1156_ = v___x_1176_;
v_getTgt_1157_ = v___x_1177_;
v___y_1158_ = v_a_1145_;
v___y_1159_ = v_a_1146_;
v___y_1160_ = v_a_1147_;
v___y_1161_ = v_a_1148_;
v___y_1162_ = v_a_1149_;
v___y_1163_ = v_a_1150_;
v___y_1164_ = v_a_1151_;
v___y_1165_ = v_a_1152_;
goto v___jp_1154_;
}
}
else
{
lean_object* v___x_1178_; lean_object* v_eq_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1178_ = lean_unsigned_to_nat(1u);
v_eq_1179_ = l_Lean_Syntax_getArg(v_x_1144_, v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(2u);
v___x_1181_ = l_Lean_Syntax_getArg(v_x_1144_, v___x_1180_);
lean_dec(v_x_1144_);
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5));
v_eq_1155_ = v_eq_1179_;
v_r_1156_ = v___x_1181_;
v_getTgt_1157_ = v___x_1182_;
v___y_1158_ = v_a_1145_;
v___y_1159_ = v_a_1146_;
v___y_1160_ = v_a_1147_;
v___y_1161_ = v_a_1148_;
v___y_1162_ = v_a_1149_;
v___y_1163_ = v_a_1150_;
v___y_1164_ = v_a_1151_;
v___y_1165_ = v_a_1152_;
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v___f_1166_; lean_object* v___x_1167_; 
lean_inc_ref(v_getTgt_1157_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1166_, 0, v_getTgt_1157_);
lean_closure_set(v___f_1166_, 1, v_r_1156_);
lean_closure_set(v___f_1166_, 2, v_eq_1155_);
v___x_1167_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1166_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
return v___x_1167_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1144_ = stack[0].m_obj;
lean_object* v_a_1145_ = stack[1].m_obj;
lean_object* v_a_1146_ = stack[2].m_obj;
lean_object* v_a_1147_ = stack[3].m_obj;
lean_object* v_a_1148_ = stack[4].m_obj;
lean_object* v_a_1149_ = stack[5].m_obj;
lean_object* v_a_1150_ = stack[6].m_obj;
lean_object* v_a_1151_ = stack[7].m_obj;
lean_object* v_a_1152_ = stack[8].m_obj;
lean_object* v_res_1183_;
v_res_1183_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(v_x_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
stack->m_obj
 = v_res_1183_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed(lean_object* v_x_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(v_x_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1194_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1(){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1203_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1));
v___x_1205_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1));
v___x_1206_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed), 10, 0);
v___x_1207_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1203_, v___x_1204_, v___x_1205_, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1208_;
v_res_1208_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
stack->m_obj
 = v_res_1208_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___boxed(lean_object* v_a_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
return v_res_1210_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3(){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1));
v___x_1238_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6));
v___x_1239_ = l_Lean_addBuiltinDeclarationRanges(v___x_1237_, v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1240_;
v_res_1240_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
stack->m_obj
 = v_res_1240_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___boxed(lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
return v_res_1242_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1243_ = stack[0].m_obj;
lean_object* v_a_1244_ = stack[1].m_obj;
lean_object* v_a_1245_ = stack[2].m_obj;
lean_object* v_a_1246_ = stack[3].m_obj;
lean_object* v_a_1247_ = stack[4].m_obj;
lean_object* v_a_1248_ = stack[5].m_obj;
lean_object* v_a_1249_ = stack[6].m_obj;
lean_object* v_a_1250_ = stack[7].m_obj;
lean_object* v_a_1251_ = stack[8].m_obj;
lean_object* v_res_1254_;
v_res_1254_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
stack->m_obj
 = v_res_1254_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
return v_res_1265_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1(){
_start:
{
lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed), 10, 0);
v___x_1275_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3));
v___x_1277_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1));
v___x_1278_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1275_, v___x_1276_, v___x_1277_, v___f_1274_);
return v___x_1278_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1279_;
v_res_1279_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
stack->m_obj
 = v_res_1279_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___boxed(lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
return v_res_1281_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3(){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1));
v___x_1309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6));
v___x_1310_ = l_Lean_addBuiltinDeclarationRanges(v___x_1308_, v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1311_;
v_res_1311_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
stack->m_obj
 = v_res_1311_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___boxed(lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
return v_res_1313_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(uint8_t v___x_1338_, lean_object* v_val_1339_, lean_object* v___x_1340_, lean_object* v_eq_1341_, lean_object* v_c_1342_, lean_object* v_ty_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v_lDecl_1437_; lean_object* v___x_1480_; 
lean_inc(v___x_1340_);
v___x_1480_ = l_Lean_Elab_Tactic_getFVarId(v___x_1340_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v_lctx_1482_; lean_object* v___x_1483_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1480_, 1);
v_lctx_1482_ = lean_ctor_get(v___y_1348_, 2);
lean_inc_ref(v_lctx_1482_);
v___x_1483_ = lean_local_ctx_find(v_lctx_1482_, v_a_1481_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v_ty_1343_);
lean_dec(v_c_1342_);
lean_dec(v_eq_1341_);
lean_dec(v_val_1339_);
v___x_1484_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1485_ = l_Lean_MessageData_ofSyntax(v___x_1340_);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1488_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec_ref(v___y_1348_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_val_1498_; 
v_val_1498_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v___x_1483_, 1);
v_lDecl_1437_ = v_val_1498_;
goto v___jp_1436_;
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref(v___y_1348_);
lean_dec(v_ty_1343_);
lean_dec(v_c_1342_);
lean_dec(v_eq_1341_);
lean_dec(v___x_1340_);
lean_dec(v_val_1339_);
v_a_1499_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1480_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1480_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
v___jp_1353_:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_LocalDecl_value_x3f(v___y_1354_, v___x_1338_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_dec_ref(v___y_1354_);
lean_dec(v_eq_1341_);
if (lean_obj_tag(v_val_1339_) == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref(v___y_1359_);
lean_dec(v___x_1340_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref_known(v_val_1339_, 1);
v___x_1366_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1367_ = l_Lean_MessageData_ofSyntax(v___x_1340_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1370_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec_ref(v___y_1359_);
return v___x_1371_;
}
}
else
{
if (lean_obj_tag(v_val_1339_) == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref_known(v___x_1363_, 1);
lean_dec_ref(v___y_1354_);
lean_dec(v_eq_1341_);
v___x_1372_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1373_ = l_Lean_MessageData_ofSyntax(v___x_1340_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1376_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec_ref(v___y_1359_);
return v___x_1377_;
}
else
{
if (lean_obj_tag(v_eq_1341_) == 0)
{
lean_object* v___x_1378_; 
lean_dec_ref_known(v_val_1339_, 1);
lean_dec_ref_known(v___x_1363_, 1);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1354_);
lean_dec(v___x_1340_);
v___x_1378_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1378_;
}
else
{
lean_object* v_val_1379_; lean_object* v_val_1380_; lean_object* v_val_1381_; lean_object* v___x_1382_; 
v_val_1379_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v___x_1363_, 1);
v_val_1380_ = lean_ctor_get(v_val_1339_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_val_1339_, 1);
v_val_1381_ = lean_ctor_get(v_eq_1341_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v_eq_1341_, 1);
v___x_1382_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_1381_);
if (lean_obj_tag(v___x_1382_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1434_; 
v_val_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1434_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_val_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1434_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = l_Lean_LocalDecl_type(v___y_1354_);
lean_dec_ref(v___y_1354_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1387_);
v___x_1389_ = v___x_1385_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Elab_Tactic_elabTerm(v_val_1380_, v___x_1389_, v___x_1338_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1392_; lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc_n(v_a_1391_, 2);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_1379_, v___y_1360_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_n(v_a_1393_, 2);
lean_dec_ref(v___x_1392_);
v___x_1394_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1391_, v_a_1393_, v_val_1383_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v_val_1383_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1416_; 
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1397_ = v___x_1394_;
v_isShared_1398_ = v_isSharedCheck_1416_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1394_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1416_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_unbox(v_a_1395_);
lean_dec(v_a_1395_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_del_object(v___x_1397_);
v___x_1400_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1401_ = l_Lean_MessageData_ofSyntax(v___x_1340_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7);
v___x_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1402_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = l_Lean_indentExpr(v_a_1393_);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = l_Lean_indentExpr(v_a_1391_);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1410_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec_ref(v___y_1359_);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_dec(v_a_1393_);
lean_dec(v_a_1391_);
lean_dec_ref(v___y_1359_);
lean_dec(v___x_1340_);
v___x_1412_ = lean_box(0);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v___x_1412_);
v___x_1414_ = v___x_1397_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_a_1393_);
lean_dec(v_a_1391_);
lean_dec_ref(v___y_1359_);
lean_dec(v___x_1340_);
v_a_1417_ = lean_ctor_get(v___x_1394_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1394_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1394_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1394_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_val_1383_);
lean_dec(v_val_1379_);
lean_dec_ref(v___y_1359_);
lean_dec(v___x_1340_);
v_a_1425_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1390_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1390_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
else
{
lean_object* v___x_1435_; 
lean_dec(v___x_1382_);
lean_dec(v_val_1380_);
lean_dec(v_val_1379_);
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___y_1354_);
lean_dec(v___x_1340_);
v___x_1435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1435_;
}
}
}
}
}
v___jp_1436_:
{
if (lean_obj_tag(v_c_1342_) == 1)
{
if (lean_obj_tag(v_ty_1343_) == 1)
{
lean_object* v_val_1438_; lean_object* v_val_1439_; lean_object* v___x_1440_; 
v_val_1438_ = lean_ctor_get(v_c_1342_, 0);
lean_inc(v_val_1438_);
lean_dec_ref_known(v_c_1342_, 1);
v_val_1439_ = lean_ctor_get(v_ty_1343_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v_ty_1343_, 1);
v___x_1440_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_1438_);
if (lean_obj_tag(v___x_1440_) == 1)
{
lean_object* v_val_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_val_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_val_1441_);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = lean_box(0);
v___x_1443_ = l_Lean_Elab_Tactic_elabTerm(v_val_1439_, v___x_1442_, v___x_1338_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc_n(v_a_1444_, 2);
lean_dec_ref_known(v___x_1443_, 1);
v___x_1445_ = l_Lean_LocalDecl_type(v_lDecl_1437_);
v___x_1446_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_1445_, v___y_1349_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_n(v_a_1447_, 2);
lean_dec_ref(v___x_1446_);
v___x_1448_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1444_, v_a_1447_, v_val_1441_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v_val_1441_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; uint8_t v___x_1450_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = lean_unbox(v_a_1449_);
lean_dec(v_a_1449_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_lDecl_1437_);
lean_dec(v_eq_1341_);
lean_dec(v_val_1339_);
v___x_1451_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1452_ = l_Lean_MessageData_ofSyntax(v___x_1340_);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
v___x_1454_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_indentExpr(v_a_1447_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = l_Lean_indentExpr(v_a_1444_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1461_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec_ref(v___y_1348_);
return v___x_1462_;
}
else
{
lean_dec(v_a_1447_);
lean_dec(v_a_1444_);
v___y_1354_ = v_lDecl_1437_;
v___y_1355_ = v___y_1344_;
v___y_1356_ = v___y_1345_;
v___y_1357_ = v___y_1346_;
v___y_1358_ = v___y_1347_;
v___y_1359_ = v___y_1348_;
v___y_1360_ = v___y_1349_;
v___y_1361_ = v___y_1350_;
v___y_1362_ = v___y_1351_;
goto v___jp_1353_;
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_a_1447_);
lean_dec(v_a_1444_);
lean_dec_ref(v_lDecl_1437_);
lean_dec_ref(v___y_1348_);
lean_dec(v_eq_1341_);
lean_dec(v___x_1340_);
lean_dec(v_val_1339_);
v_a_1463_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1448_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1448_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_val_1441_);
lean_dec_ref(v_lDecl_1437_);
lean_dec_ref(v___y_1348_);
lean_dec(v_eq_1341_);
lean_dec(v___x_1340_);
lean_dec(v_val_1339_);
v_a_1471_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1443_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1443_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v___x_1479_; 
lean_dec(v___x_1440_);
lean_dec(v_val_1439_);
lean_dec_ref(v_lDecl_1437_);
lean_dec_ref(v___y_1348_);
lean_dec(v_eq_1341_);
lean_dec(v___x_1340_);
lean_dec(v_val_1339_);
v___x_1479_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1479_;
}
}
else
{
lean_dec_ref_known(v_c_1342_, 1);
lean_dec(v_ty_1343_);
v___y_1354_ = v_lDecl_1437_;
v___y_1355_ = v___y_1344_;
v___y_1356_ = v___y_1345_;
v___y_1357_ = v___y_1346_;
v___y_1358_ = v___y_1347_;
v___y_1359_ = v___y_1348_;
v___y_1360_ = v___y_1349_;
v___y_1361_ = v___y_1350_;
v___y_1362_ = v___y_1351_;
goto v___jp_1353_;
}
}
else
{
lean_dec(v_ty_1343_);
lean_dec(v_c_1342_);
v___y_1354_ = v_lDecl_1437_;
v___y_1355_ = v___y_1344_;
v___y_1356_ = v___y_1345_;
v___y_1357_ = v___y_1346_;
v___y_1358_ = v___y_1347_;
v___y_1359_ = v___y_1348_;
v___y_1360_ = v___y_1349_;
v___y_1361_ = v___y_1350_;
v___y_1362_ = v___y_1351_;
goto v___jp_1353_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1338_ = stack[0].m_num;
lean_object* v_val_1339_ = stack[1].m_obj;
lean_object* v___x_1340_ = stack[2].m_obj;
lean_object* v_eq_1341_ = stack[3].m_obj;
lean_object* v_c_1342_ = stack[4].m_obj;
lean_object* v_ty_1343_ = stack[5].m_obj;
lean_object* v___y_1344_ = stack[6].m_obj;
lean_object* v___y_1345_ = stack[7].m_obj;
lean_object* v___y_1346_ = stack[8].m_obj;
lean_object* v___y_1347_ = stack[9].m_obj;
lean_object* v___y_1348_ = stack[10].m_obj;
lean_object* v___y_1349_ = stack[11].m_obj;
lean_object* v___y_1350_ = stack[12].m_obj;
lean_object* v___y_1351_ = stack[13].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(v___x_1338_, v_val_1339_, v___x_1340_, v_eq_1341_, v_c_1342_, v_ty_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed(lean_object* v___x_1508_, lean_object* v_val_1509_, lean_object* v___x_1510_, lean_object* v_eq_1511_, lean_object* v_c_1512_, lean_object* v_ty_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_8229__boxed_1523_; lean_object* v_res_1524_; 
v___x_8229__boxed_1523_ = lean_unbox(v___x_1508_);
v_res_1524_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(v___x_8229__boxed_1523_, v_val_1509_, v___x_1510_, v_eq_1511_, v_c_1512_, v_ty_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
return v_res_1524_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(lean_object* v_val_1525_, lean_object* v___x_1526_, lean_object* v_eq_1527_, lean_object* v_c_1528_, lean_object* v_ty_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v_lDecl_1624_; lean_object* v___x_1668_; 
lean_inc(v___x_1526_);
v___x_1668_ = l_Lean_Elab_Tactic_getFVarId(v___x_1526_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v_lctx_1670_; lean_object* v___x_1671_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v_lctx_1670_ = lean_ctor_get(v___y_1534_, 2);
lean_inc_ref(v_lctx_1670_);
v___x_1671_ = lean_local_ctx_find(v_lctx_1670_, v_a_1669_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec(v_ty_1529_);
lean_dec(v_c_1528_);
lean_dec(v_eq_1527_);
lean_dec(v_val_1525_);
v___x_1672_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1673_ = l_Lean_MessageData_ofSyntax(v___x_1526_);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1676_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___y_1534_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
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
else
{
lean_object* v_val_1686_; 
v_val_1686_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_val_1686_);
lean_dec_ref_known(v___x_1671_, 1);
v_lDecl_1624_ = v_val_1686_;
goto v___jp_1623_;
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v___y_1534_);
lean_dec(v_ty_1529_);
lean_dec(v_c_1528_);
lean_dec(v_eq_1527_);
lean_dec(v___x_1526_);
lean_dec(v_val_1525_);
v_a_1687_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1668_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1668_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
v___jp_1539_:
{
uint8_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = 0;
v___x_1550_ = l_Lean_LocalDecl_value_x3f(v___y_1540_, v___x_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec_ref(v___y_1540_);
lean_dec(v_eq_1527_);
if (lean_obj_tag(v_val_1525_) == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec_ref(v___y_1545_);
lean_dec(v___x_1526_);
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec_ref_known(v_val_1525_, 1);
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1554_ = l_Lean_MessageData_ofSyntax(v___x_1526_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1557_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec_ref(v___y_1545_);
return v___x_1558_;
}
}
else
{
if (lean_obj_tag(v_val_1525_) == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref_known(v___x_1550_, 1);
lean_dec_ref(v___y_1540_);
lean_dec(v_eq_1527_);
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1560_ = l_Lean_MessageData_ofSyntax(v___x_1526_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1563_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec_ref(v___y_1545_);
return v___x_1564_;
}
else
{
if (lean_obj_tag(v_eq_1527_) == 0)
{
lean_object* v___x_1565_; 
lean_dec_ref_known(v_val_1525_, 1);
lean_dec_ref_known(v___x_1550_, 1);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1540_);
lean_dec(v___x_1526_);
v___x_1565_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1565_;
}
else
{
lean_object* v_val_1566_; lean_object* v_val_1567_; lean_object* v_val_1568_; lean_object* v___x_1569_; 
v_val_1566_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v___x_1550_, 1);
v_val_1567_ = lean_ctor_get(v_val_1525_, 0);
lean_inc(v_val_1567_);
lean_dec_ref_known(v_val_1525_, 1);
v_val_1568_ = lean_ctor_get(v_eq_1527_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v_eq_1527_, 1);
v___x_1569_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_1568_);
if (lean_obj_tag(v___x_1569_) == 1)
{
lean_object* v_val_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1621_; 
v_val_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1621_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_val_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1621_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = l_Lean_LocalDecl_type(v___y_1540_);
lean_dec_ref(v___y_1540_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Elab_Tactic_elabTerm(v_val_1567_, v___x_1576_, v___x_1549_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_n(v_a_1578_, 2);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_1566_, v___y_1546_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc_n(v_a_1580_, 2);
lean_dec_ref(v___x_1579_);
v___x_1581_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1578_, v_a_1580_, v_val_1570_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec(v_val_1570_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1603_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1603_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1603_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_del_object(v___x_1584_);
v___x_1587_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1588_ = l_Lean_MessageData_ofSyntax(v___x_1526_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7);
v___x_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_indentExpr(v_a_1580_);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_indentExpr(v_a_1578_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1597_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
lean_dec_ref(v___y_1545_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_dec(v_a_1580_);
lean_dec(v_a_1578_);
lean_dec_ref(v___y_1545_);
lean_dec(v___x_1526_);
v___x_1599_ = lean_box(0);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1599_);
v___x_1601_ = v___x_1584_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1580_);
lean_dec(v_a_1578_);
lean_dec_ref(v___y_1545_);
lean_dec(v___x_1526_);
v_a_1604_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1581_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1581_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_val_1570_);
lean_dec(v_val_1566_);
lean_dec_ref(v___y_1545_);
lean_dec(v___x_1526_);
v_a_1612_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1577_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1577_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
}
else
{
lean_object* v___x_1622_; 
lean_dec(v___x_1569_);
lean_dec(v_val_1567_);
lean_dec(v_val_1566_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1540_);
lean_dec(v___x_1526_);
v___x_1622_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1622_;
}
}
}
}
}
v___jp_1623_:
{
if (lean_obj_tag(v_c_1528_) == 1)
{
if (lean_obj_tag(v_ty_1529_) == 1)
{
lean_object* v_val_1625_; lean_object* v_val_1626_; lean_object* v___x_1627_; 
v_val_1625_ = lean_ctor_get(v_c_1528_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v_c_1528_, 1);
v_val_1626_ = lean_ctor_get(v_ty_1529_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v_ty_1529_, 1);
v___x_1627_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_1625_);
if (lean_obj_tag(v___x_1627_) == 1)
{
lean_object* v_val_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; 
v_val_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_val_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1629_ = lean_box(0);
v___x_1630_ = 0;
v___x_1631_ = l_Lean_Elab_Tactic_elabTerm(v_val_1626_, v___x_1629_, v___x_1630_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_a_1635_; lean_object* v___x_1636_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc_n(v_a_1632_, 2);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = l_Lean_LocalDecl_type(v_lDecl_1624_);
v___x_1634_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_1633_, v___y_1535_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc_n(v_a_1635_, 2);
lean_dec_ref(v___x_1634_);
v___x_1636_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1632_, v_a_1635_, v_val_1628_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v_val_1628_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; uint8_t v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = lean_unbox(v_a_1637_);
lean_dec(v_a_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v_lDecl_1624_);
lean_dec(v_eq_1527_);
lean_dec(v_val_1525_);
v___x_1639_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1640_ = l_Lean_MessageData_ofSyntax(v___x_1526_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_indentExpr(v_a_1635_);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_indentExpr(v_a_1632_);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1649_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec_ref(v___y_1534_);
return v___x_1650_;
}
else
{
lean_dec(v_a_1635_);
lean_dec(v_a_1632_);
v___y_1540_ = v_lDecl_1624_;
v___y_1541_ = v___y_1530_;
v___y_1542_ = v___y_1531_;
v___y_1543_ = v___y_1532_;
v___y_1544_ = v___y_1533_;
v___y_1545_ = v___y_1534_;
v___y_1546_ = v___y_1535_;
v___y_1547_ = v___y_1536_;
v___y_1548_ = v___y_1537_;
goto v___jp_1539_;
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_a_1635_);
lean_dec(v_a_1632_);
lean_dec_ref(v_lDecl_1624_);
lean_dec_ref(v___y_1534_);
lean_dec(v_eq_1527_);
lean_dec(v___x_1526_);
lean_dec(v_val_1525_);
v_a_1651_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1636_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1636_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_val_1628_);
lean_dec_ref(v_lDecl_1624_);
lean_dec_ref(v___y_1534_);
lean_dec(v_eq_1527_);
lean_dec(v___x_1526_);
lean_dec(v_val_1525_);
v_a_1659_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1631_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1631_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v___x_1667_; 
lean_dec(v___x_1627_);
lean_dec(v_val_1626_);
lean_dec_ref(v_lDecl_1624_);
lean_dec_ref(v___y_1534_);
lean_dec(v_eq_1527_);
lean_dec(v___x_1526_);
lean_dec(v_val_1525_);
v___x_1667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1667_;
}
}
else
{
lean_dec_ref_known(v_c_1528_, 1);
lean_dec(v_ty_1529_);
v___y_1540_ = v_lDecl_1624_;
v___y_1541_ = v___y_1530_;
v___y_1542_ = v___y_1531_;
v___y_1543_ = v___y_1532_;
v___y_1544_ = v___y_1533_;
v___y_1545_ = v___y_1534_;
v___y_1546_ = v___y_1535_;
v___y_1547_ = v___y_1536_;
v___y_1548_ = v___y_1537_;
goto v___jp_1539_;
}
}
else
{
lean_dec(v_ty_1529_);
lean_dec(v_c_1528_);
v___y_1540_ = v_lDecl_1624_;
v___y_1541_ = v___y_1530_;
v___y_1542_ = v___y_1531_;
v___y_1543_ = v___y_1532_;
v___y_1544_ = v___y_1533_;
v___y_1545_ = v___y_1534_;
v___y_1546_ = v___y_1535_;
v___y_1547_ = v___y_1536_;
v___y_1548_ = v___y_1537_;
goto v___jp_1539_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1525_ = stack[0].m_obj;
lean_object* v___x_1526_ = stack[1].m_obj;
lean_object* v_eq_1527_ = stack[2].m_obj;
lean_object* v_c_1528_ = stack[3].m_obj;
lean_object* v_ty_1529_ = stack[4].m_obj;
lean_object* v___y_1530_ = stack[5].m_obj;
lean_object* v___y_1531_ = stack[6].m_obj;
lean_object* v___y_1532_ = stack[7].m_obj;
lean_object* v___y_1533_ = stack[8].m_obj;
lean_object* v___y_1534_ = stack[9].m_obj;
lean_object* v___y_1535_ = stack[10].m_obj;
lean_object* v___y_1536_ = stack[11].m_obj;
lean_object* v___y_1537_ = stack[12].m_obj;
lean_object* v_res_1695_;
v_res_1695_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(v_val_1525_, v___x_1526_, v_eq_1527_, v_c_1528_, v_ty_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
stack->m_obj
 = v_res_1695_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed(lean_object* v_val_1696_, lean_object* v___x_1697_, lean_object* v_eq_1698_, lean_object* v_c_1699_, lean_object* v_ty_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(v_val_1696_, v___x_1697_, v_eq_1698_, v_c_1699_, v_ty_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1710_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object* v_x_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1));
lean_inc(v_x_1723_);
v___x_1734_ = l_Lean_Syntax_isOfKind(v_x_1723_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3));
lean_inc(v_x_1723_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v_x_1723_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec(v_x_1723_);
v___x_1737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1737_;
}
else
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v_eq_1752_; lean_object* v_val_1753_; lean_object* v___x_1757_; lean_object* v_c_1759_; lean_object* v_ty_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v___x_1738_ = lean_unsigned_to_nat(0u);
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = l_Lean_Syntax_getArg(v_x_1723_, v___x_1739_);
v___x_1757_ = lean_unsigned_to_nat(2u);
v___x_1779_ = l_Lean_Syntax_getArg(v_x_1723_, v___x_1757_);
v___x_1780_ = l_Lean_Syntax_isNone(v___x_1779_);
if (v___x_1780_ == 0)
{
uint8_t v___x_1781_; 
lean_inc(v___x_1779_);
v___x_1781_ = l_Lean_Syntax_matchesNull(v___x_1779_, v___x_1757_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_dec(v___x_1779_);
lean_dec(v___x_1740_);
lean_dec(v_x_1723_);
v___x_1782_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1782_;
}
else
{
lean_object* v_c_1783_; lean_object* v_ty_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_c_1783_ = l_Lean_Syntax_getArg(v___x_1779_, v___x_1738_);
v_ty_1784_ = l_Lean_Syntax_getArg(v___x_1779_, v___x_1739_);
lean_dec(v___x_1779_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_c_1783_);
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_ty_1784_);
v_c_1759_ = v___x_1785_;
v_ty_1760_ = v___x_1786_;
v___y_1761_ = v_a_1724_;
v___y_1762_ = v_a_1725_;
v___y_1763_ = v_a_1726_;
v___y_1764_ = v_a_1727_;
v___y_1765_ = v_a_1728_;
v___y_1766_ = v_a_1729_;
v___y_1767_ = v_a_1730_;
v___y_1768_ = v_a_1731_;
goto v___jp_1758_;
}
}
else
{
lean_object* v___x_1787_; 
lean_dec(v___x_1779_);
v___x_1787_ = lean_box(0);
v_c_1759_ = v___x_1787_;
v_ty_1760_ = v___x_1787_;
v___y_1761_ = v_a_1724_;
v___y_1762_ = v_a_1725_;
v___y_1763_ = v_a_1726_;
v___y_1764_ = v_a_1727_;
v___y_1765_ = v_a_1728_;
v___y_1766_ = v_a_1729_;
v___y_1767_ = v_a_1730_;
v___y_1768_ = v_a_1731_;
goto v___jp_1758_;
}
v___jp_1741_:
{
lean_object* v___x_1754_; lean_object* v___f_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_box(v___x_1734_);
v___f_1755_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed), 15, 6);
lean_closure_set(v___f_1755_, 0, v___x_1754_);
lean_closure_set(v___f_1755_, 1, v_val_1753_);
lean_closure_set(v___f_1755_, 2, v___x_1740_);
lean_closure_set(v___f_1755_, 3, v_eq_1752_);
lean_closure_set(v___f_1755_, 4, v___y_1749_);
lean_closure_set(v___f_1755_, 5, v___y_1744_);
v___x_1756_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1755_, v___y_1747_, v___y_1746_, v___y_1748_, v___y_1743_, v___y_1750_, v___y_1751_, v___y_1745_, v___y_1742_);
return v___x_1756_;
}
v___jp_1758_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_unsigned_to_nat(3u);
v___x_1770_ = l_Lean_Syntax_getArg(v_x_1723_, v___x_1769_);
lean_dec(v_x_1723_);
v___x_1771_ = l_Lean_Syntax_isNone(v___x_1770_);
if (v___x_1771_ == 0)
{
uint8_t v___x_1772_; 
lean_inc(v___x_1770_);
v___x_1772_ = l_Lean_Syntax_matchesNull(v___x_1770_, v___x_1757_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_dec(v___x_1770_);
lean_dec(v_ty_1760_);
lean_dec(v_c_1759_);
lean_dec(v___x_1740_);
v___x_1773_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1773_;
}
else
{
lean_object* v_eq_1774_; lean_object* v_val_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_eq_1774_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1738_);
v_val_1775_ = l_Lean_Syntax_getArg(v___x_1770_, v___x_1739_);
lean_dec(v___x_1770_);
v___x_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_eq_1774_);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_val_1775_);
v___y_1742_ = v___y_1768_;
v___y_1743_ = v___y_1764_;
v___y_1744_ = v_ty_1760_;
v___y_1745_ = v___y_1767_;
v___y_1746_ = v___y_1762_;
v___y_1747_ = v___y_1761_;
v___y_1748_ = v___y_1763_;
v___y_1749_ = v_c_1759_;
v___y_1750_ = v___y_1765_;
v___y_1751_ = v___y_1766_;
v_eq_1752_ = v___x_1776_;
v_val_1753_ = v___x_1777_;
goto v___jp_1741_;
}
}
else
{
lean_object* v___x_1778_; 
lean_dec(v___x_1770_);
v___x_1778_ = lean_box(0);
v___y_1742_ = v___y_1768_;
v___y_1743_ = v___y_1764_;
v___y_1744_ = v_ty_1760_;
v___y_1745_ = v___y_1767_;
v___y_1746_ = v___y_1762_;
v___y_1747_ = v___y_1761_;
v___y_1748_ = v___y_1763_;
v___y_1749_ = v_c_1759_;
v___y_1750_ = v___y_1765_;
v___y_1751_ = v___y_1766_;
v_eq_1752_ = v___x_1778_;
v_val_1753_ = v___x_1778_;
goto v___jp_1741_;
}
}
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v_eq_1802_; lean_object* v_val_1803_; lean_object* v___x_1806_; lean_object* v_c_1808_; lean_object* v_ty_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = l_Lean_Syntax_getArg(v_x_1723_, v___x_1789_);
v___x_1806_ = lean_unsigned_to_nat(2u);
v___x_1828_ = l_Lean_Syntax_getArg(v_x_1723_, v___x_1806_);
v___x_1829_ = l_Lean_Syntax_isNone(v___x_1828_);
if (v___x_1829_ == 0)
{
uint8_t v___x_1830_; 
lean_inc(v___x_1828_);
v___x_1830_ = l_Lean_Syntax_matchesNull(v___x_1828_, v___x_1806_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_dec(v___x_1828_);
lean_dec(v___x_1790_);
lean_dec(v_x_1723_);
v___x_1831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1831_;
}
else
{
lean_object* v_c_1832_; lean_object* v_ty_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_c_1832_ = l_Lean_Syntax_getArg(v___x_1828_, v___x_1788_);
v_ty_1833_ = l_Lean_Syntax_getArg(v___x_1828_, v___x_1789_);
lean_dec(v___x_1828_);
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_c_1832_);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_ty_1833_);
v_c_1808_ = v___x_1834_;
v_ty_1809_ = v___x_1835_;
v___y_1810_ = v_a_1724_;
v___y_1811_ = v_a_1725_;
v___y_1812_ = v_a_1726_;
v___y_1813_ = v_a_1727_;
v___y_1814_ = v_a_1728_;
v___y_1815_ = v_a_1729_;
v___y_1816_ = v_a_1730_;
v___y_1817_ = v_a_1731_;
goto v___jp_1807_;
}
}
else
{
lean_object* v___x_1836_; 
lean_dec(v___x_1828_);
v___x_1836_ = lean_box(0);
v_c_1808_ = v___x_1836_;
v_ty_1809_ = v___x_1836_;
v___y_1810_ = v_a_1724_;
v___y_1811_ = v_a_1725_;
v___y_1812_ = v_a_1726_;
v___y_1813_ = v_a_1727_;
v___y_1814_ = v_a_1728_;
v___y_1815_ = v_a_1729_;
v___y_1816_ = v_a_1730_;
v___y_1817_ = v_a_1731_;
goto v___jp_1807_;
}
v___jp_1791_:
{
lean_object* v___f_1804_; lean_object* v___x_1805_; 
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1804_, 0, v_val_1803_);
lean_closure_set(v___f_1804_, 1, v___x_1790_);
lean_closure_set(v___f_1804_, 2, v_eq_1802_);
lean_closure_set(v___f_1804_, 3, v___y_1801_);
lean_closure_set(v___f_1804_, 4, v___y_1795_);
v___x_1805_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1804_, v___y_1797_, v___y_1792_, v___y_1793_, v___y_1796_, v___y_1800_, v___y_1794_, v___y_1799_, v___y_1798_);
return v___x_1805_;
}
v___jp_1807_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = lean_unsigned_to_nat(3u);
v___x_1819_ = l_Lean_Syntax_getArg(v_x_1723_, v___x_1818_);
lean_dec(v_x_1723_);
v___x_1820_ = l_Lean_Syntax_isNone(v___x_1819_);
if (v___x_1820_ == 0)
{
uint8_t v___x_1821_; 
lean_inc(v___x_1819_);
v___x_1821_ = l_Lean_Syntax_matchesNull(v___x_1819_, v___x_1806_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; 
lean_dec(v___x_1819_);
lean_dec(v_ty_1809_);
lean_dec(v_c_1808_);
lean_dec(v___x_1790_);
v___x_1822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1822_;
}
else
{
lean_object* v_eq_1823_; lean_object* v_val_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_eq_1823_ = l_Lean_Syntax_getArg(v___x_1819_, v___x_1788_);
v_val_1824_ = l_Lean_Syntax_getArg(v___x_1819_, v___x_1789_);
lean_dec(v___x_1819_);
v___x_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_eq_1823_);
v___x_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_val_1824_);
v___y_1792_ = v___y_1811_;
v___y_1793_ = v___y_1812_;
v___y_1794_ = v___y_1815_;
v___y_1795_ = v_ty_1809_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1810_;
v___y_1798_ = v___y_1817_;
v___y_1799_ = v___y_1816_;
v___y_1800_ = v___y_1814_;
v___y_1801_ = v_c_1808_;
v_eq_1802_ = v___x_1825_;
v_val_1803_ = v___x_1826_;
goto v___jp_1791_;
}
}
else
{
lean_object* v___x_1827_; 
lean_dec(v___x_1819_);
v___x_1827_ = lean_box(0);
v___y_1792_ = v___y_1811_;
v___y_1793_ = v___y_1812_;
v___y_1794_ = v___y_1815_;
v___y_1795_ = v_ty_1809_;
v___y_1796_ = v___y_1813_;
v___y_1797_ = v___y_1810_;
v___y_1798_ = v___y_1817_;
v___y_1799_ = v___y_1816_;
v___y_1800_ = v___y_1814_;
v___y_1801_ = v_c_1808_;
v_eq_1802_ = v___x_1827_;
v_val_1803_ = v___x_1827_;
goto v___jp_1791_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1723_ = stack[0].m_obj;
lean_object* v_a_1724_ = stack[1].m_obj;
lean_object* v_a_1725_ = stack[2].m_obj;
lean_object* v_a_1726_ = stack[3].m_obj;
lean_object* v_a_1727_ = stack[4].m_obj;
lean_object* v_a_1728_ = stack[5].m_obj;
lean_object* v_a_1729_ = stack[6].m_obj;
lean_object* v_a_1730_ = stack[7].m_obj;
lean_object* v_a_1731_ = stack[8].m_obj;
lean_object* v_res_1837_;
v_res_1837_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(v_x_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
stack->m_obj
 = v_res_1837_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed(lean_object* v_x_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(v_x_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1848_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1(){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1857_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1858_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1));
v___x_1859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1));
v___x_1860_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed), 10, 0);
v___x_1861_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1857_, v___x_1858_, v___x_1859_, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1862_;
v_res_1862_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
stack->m_obj
 = v_res_1862_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___boxed(lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
return v_res_1864_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3(){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1));
v___x_1892_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6));
v___x_1893_ = l_Lean_addBuiltinDeclarationRanges(v___x_1891_, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1894_;
v_res_1894_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
stack->m_obj
 = v_res_1894_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___boxed(lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
return v_res_1896_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1897_ = stack[0].m_obj;
lean_object* v_a_1898_ = stack[1].m_obj;
lean_object* v_a_1899_ = stack[2].m_obj;
lean_object* v_a_1900_ = stack[3].m_obj;
lean_object* v_a_1901_ = stack[4].m_obj;
lean_object* v_a_1902_ = stack[5].m_obj;
lean_object* v_a_1903_ = stack[6].m_obj;
lean_object* v_a_1904_ = stack[7].m_obj;
lean_object* v_a_1905_ = stack[8].m_obj;
lean_object* v_res_1908_;
v_res_1908_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
stack->m_obj
 = v_res_1908_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
return v_res_1919_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1(){
_start:
{
lean_object* v___f_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___f_1928_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed), 10, 0);
v___x_1929_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1930_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3));
v___x_1931_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1));
v___x_1932_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1929_, v___x_1930_, v___x_1931_, v___f_1928_);
return v___x_1932_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1933_;
v_res_1933_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
stack->m_obj
 = v_res_1933_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___boxed(lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
return v_res_1935_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3(){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1));
v___x_1963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6));
v___x_1964_ = l_Lean_addBuiltinDeclarationRanges(v___x_1962_, v___x_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1965_;
v_res_1965_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
stack->m_obj
 = v_res_1965_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___boxed(lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
return v_res_1967_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1971_;
v_res_1971_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg___boxed(lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v_res_1973_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(lean_object* v_00_u03b1_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_1978_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1975_ = stack[1].m_obj;
lean_object* v___y_1976_ = stack[2].m_obj;
lean_object* v_res_1979_;
v_res_1979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(lean_box(0), v___y_1975_, v___y_1976_);
stack->m_obj
 = v_res_1979_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___boxed(lean_object* v_00_u03b1_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(v_00_u03b1_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1984_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg(){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1988_;
v_res_1988_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
stack->m_obj
 = v_res_1988_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg___boxed(lean_object* v___y_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v_res_1990_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(lean_object* v_00_u03b1_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v___x_1999_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1992_ = stack[1].m_obj;
lean_object* v___y_1993_ = stack[2].m_obj;
lean_object* v___y_1994_ = stack[3].m_obj;
lean_object* v___y_1995_ = stack[4].m_obj;
lean_object* v___y_1996_ = stack[5].m_obj;
lean_object* v___y_1997_ = stack[6].m_obj;
lean_object* v_res_2000_;
v_res_2000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(lean_box(0), v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
stack->m_obj
 = v_res_2000_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___boxed(lean_object* v_00_u03b1_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(v_00_u03b1_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2009_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(lean_object* v_opts_2010_, lean_object* v_opt_2011_){
_start:
{
lean_object* v_name_2012_; lean_object* v_defValue_2013_; lean_object* v_map_2014_; lean_object* v___x_2015_; 
v_name_2012_ = lean_ctor_get(v_opt_2011_, 0);
v_defValue_2013_ = lean_ctor_get(v_opt_2011_, 1);
v_map_2014_ = lean_ctor_get(v_opts_2010_, 0);
v___x_2015_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2014_, v_name_2012_);
if (lean_obj_tag(v___x_2015_) == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_unbox(v_defValue_2013_);
return v___x_2016_;
}
else
{
lean_object* v_val_2017_; 
v_val_2017_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v___x_2015_, 1);
if (lean_obj_tag(v_val_2017_) == 1)
{
uint8_t v_v_2018_; 
v_v_2018_ = lean_ctor_get_uint8(v_val_2017_, 0);
lean_dec_ref_known(v_val_2017_, 0);
return v_v_2018_;
}
else
{
uint8_t v___x_2019_; 
lean_dec(v_val_2017_);
v___x_2019_ = lean_unbox(v_defValue_2013_);
return v___x_2019_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2010_ = stack[0].m_obj;
lean_object* v_opt_2011_ = stack[1].m_obj;
uint8_t v_res_2020_;
v_res_2020_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_opts_2010_, v_opt_2011_);
stack->m_num = v_res_2020_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_2021_, lean_object* v_opt_2022_){
_start:
{
uint8_t v_res_2023_; lean_object* v_r_2024_; 
v_res_2023_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_opts_2021_, v_opt_2022_);
lean_dec_ref(v_opt_2022_);
lean_dec_ref(v_opts_2021_);
v_r_2024_ = lean_box(v_res_2023_);
return v_r_2024_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_box(1);
v___x_2026_ = l_Lean_MessageData_ofFormat(v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2));
v___x_2031_ = l_Lean_MessageData_ofFormat(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
return v_x_2032_;
}
else
{
lean_object* v_head_2034_; lean_object* v_tail_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2057_; 
v_head_2034_ = lean_ctor_get(v_x_2033_, 0);
v_tail_2035_ = lean_ctor_get(v_x_2033_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_x_2033_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2037_ = v_x_2033_;
v_isShared_2038_ = v_isSharedCheck_2057_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_tail_2035_);
lean_inc(v_head_2034_);
lean_dec(v_x_2033_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2057_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_before_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2055_; 
v_before_2039_ = lean_ctor_get(v_head_2034_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_head_2034_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v_head_2034_, 1);
lean_dec(v_unused_2056_);
v___x_2041_ = v_head_2034_;
v_isShared_2042_ = v_isSharedCheck_2055_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_before_2039_);
lean_dec(v_head_2034_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2055_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 7);
lean_ctor_set(v___x_2041_, 1, v___x_2043_);
lean_ctor_set(v___x_2041_, 0, v_x_2032_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_x_2032_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3);
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 7);
lean_ctor_set(v___x_2037_, 1, v___x_2046_);
lean_ctor_set(v___x_2037_, 0, v___x_2045_);
v___x_2048_ = v___x_2037_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = l_Lean_MessageData_ofSyntax(v_before_2039_);
v___x_2050_ = l_Lean_indentD(v___x_2049_);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2048_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v_x_2032_ = v___x_2051_;
v_x_2033_ = v_tail_2035_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1));
v___x_2062_ = l_Lean_MessageData_ofFormat(v___x_2061_);
return v___x_2062_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(lean_object* v_msgData_2063_, lean_object* v_macroStack_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2067_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2065_);
v___x_2068_ = l_Lean_Elab_pp_macroStack;
v___x_2069_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v___x_2067_, v___x_2068_);
lean_dec_ref(v___x_2067_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
lean_dec(v_macroStack_2064_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_msgData_2063_);
return v___x_2070_;
}
else
{
if (lean_obj_tag(v_macroStack_2064_) == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_msgData_2063_);
return v___x_2071_;
}
else
{
lean_object* v_head_2072_; lean_object* v_after_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2088_; 
v_head_2072_ = lean_ctor_get(v_macroStack_2064_, 0);
lean_inc(v_head_2072_);
v_after_2073_ = lean_ctor_get(v_head_2072_, 1);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_head_2072_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; 
v_unused_2089_ = lean_ctor_get(v_head_2072_, 0);
lean_dec(v_unused_2089_);
v___x_2075_ = v_head_2072_;
v_isShared_2076_ = v_isSharedCheck_2088_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_after_2073_);
lean_dec(v_head_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2088_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 7);
lean_ctor_set(v___x_2075_, 1, v___x_2077_);
lean_ctor_set(v___x_2075_, 0, v_msgData_2063_);
v___x_2079_ = v___x_2075_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_msgData_2063_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_msgData_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2080_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = l_Lean_MessageData_ofSyntax(v_after_2073_);
v___x_2083_ = l_Lean_indentD(v___x_2082_);
v_msgData_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2084_, 0, v___x_2081_);
lean_ctor_set(v_msgData_2084_, 1, v___x_2083_);
v___x_2085_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(v_msgData_2084_, v_macroStack_2064_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2063_ = stack[0].m_obj;
lean_object* v_macroStack_2064_ = stack[1].m_obj;
lean_object* v___y_2065_ = stack[2].m_obj;
lean_object* v_res_2090_;
v_res_2090_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_2063_, v_macroStack_2064_, v___y_2065_);
stack->m_obj
 = v_res_2090_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2091_, lean_object* v_macroStack_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_2091_, v_macroStack_2092_, v___y_2093_);
lean_dec_ref(v___y_2093_);
return v_res_2095_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(lean_object* v_msg_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_ref_2104_; lean_object* v_macroStack_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v_a_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_ref_2104_ = lean_ctor_get(v___y_2101_, 2);
v_macroStack_2105_ = lean_ctor_get(v___y_2097_, 1);
v___x_2106_ = l_Lean_Elab_getBetterRef(v_ref_2104_, v_macroStack_2105_);
v___x_2107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_2096_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref(v___x_2107_);
lean_inc(v_macroStack_2105_);
v___x_2109_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_a_2108_, v_macroStack_2105_, v___y_2101_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2106_);
lean_ctor_set(v___x_2114_, 1, v_a_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 1);
lean_ctor_set(v___x_2112_, 0, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2096_ = stack[0].m_obj;
lean_object* v___y_2097_ = stack[1].m_obj;
lean_object* v___y_2098_ = stack[2].m_obj;
lean_object* v___y_2099_ = stack[3].m_obj;
lean_object* v___y_2100_ = stack[4].m_obj;
lean_object* v___y_2101_ = stack[5].m_obj;
lean_object* v___y_2102_ = stack[6].m_obj;
lean_object* v_res_2119_;
v_res_2119_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v_msg_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
stack->m_obj
 = v_res_2119_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg___boxed(lean_object* v_msg_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v_msg_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2128_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(lean_object* v_eq_2129_, lean_object* v_r_2130_, lean_object* v_p_2131_, lean_object* v_x_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_2129_);
if (lean_obj_tag(v___x_2140_) == 1)
{
lean_object* v_val_2141_; lean_object* v___x_2142_; 
v_val_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc_n(v_val_2141_, 2);
lean_dec_ref_known(v___x_2140_, 1);
lean_inc(v_p_2131_);
lean_inc(v_r_2130_);
v___x_2142_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_val_2141_, v_r_2130_, v_p_2131_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2167_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2167_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2167_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_unbox(v_a_2143_);
lean_dec(v_a_2143_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_del_object(v___x_2145_);
v___x_2148_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1);
v___x_2149_ = l_Lean_MessageData_ofSyntax(v_r_2130_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_2141_);
lean_dec(v_val_2141_);
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2152_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = l_Lean_MessageData_ofSyntax(v_p_2131_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_2161_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
lean_dec(v_val_2141_);
lean_dec(v_p_2131_);
lean_dec(v_r_2130_);
v___x_2163_ = lean_box(0);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2163_);
v___x_2165_ = v___x_2145_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2163_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_val_2141_);
lean_dec(v_p_2131_);
lean_dec(v_r_2130_);
v_a_2168_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2142_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2142_);
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
lean_object* v___x_2176_; 
lean_dec(v___x_2140_);
lean_dec(v_p_2131_);
lean_dec(v_r_2130_);
v___x_2176_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v___x_2176_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_eq_2129_ = stack[0].m_obj;
lean_object* v_r_2130_ = stack[1].m_obj;
lean_object* v_p_2131_ = stack[2].m_obj;
lean_object* v_x_2132_ = stack[3].m_obj;
lean_object* v___y_2133_ = stack[4].m_obj;
lean_object* v___y_2134_ = stack[5].m_obj;
lean_object* v___y_2135_ = stack[6].m_obj;
lean_object* v___y_2136_ = stack[7].m_obj;
lean_object* v___y_2137_ = stack[8].m_obj;
lean_object* v___y_2138_ = stack[9].m_obj;
lean_object* v_res_2177_;
v_res_2177_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(v_eq_2129_, v_r_2130_, v_p_2131_, v_x_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
stack->m_obj
 = v_res_2177_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed(lean_object* v_eq_2178_, lean_object* v_r_2179_, lean_object* v_p_2180_, lean_object* v_x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(v_eq_2178_, v_r_2179_, v_p_2180_, v_x_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v_x_2181_);
return v_res_2189_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object* v_x_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2));
lean_inc(v_x_2197_);
v___x_2202_ = l_Lean_Syntax_isOfKind(v_x_2197_, v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
lean_dec(v_x_2197_);
v___x_2203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; lean_object* v_eq_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2204_ = lean_unsigned_to_nat(2u);
v_eq_2205_ = l_Lean_Syntax_getArg(v_x_2197_, v___x_2204_);
v___x_2206_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_2205_);
v___x_2207_ = l_Lean_Syntax_isOfKind(v_eq_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_eq_2205_);
lean_dec(v_x_2197_);
v___x_2208_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; lean_object* v_r_2210_; lean_object* v___x_2211_; lean_object* v_p_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; 
v___x_2209_ = lean_unsigned_to_nat(1u);
v_r_2210_ = l_Lean_Syntax_getArg(v_x_2197_, v___x_2209_);
v___x_2211_ = lean_unsigned_to_nat(3u);
v_p_2212_ = l_Lean_Syntax_getArg(v_x_2197_, v___x_2211_);
lean_dec(v_x_2197_);
v___f_2213_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2213_, 0, v_eq_2205_);
lean_closure_set(v___f_2213_, 1, v_r_2210_);
lean_closure_set(v___f_2213_, 2, v_p_2212_);
v___x_2214_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_2213_, v_a_2198_, v_a_2199_);
return v___x_2214_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2197_ = stack[0].m_obj;
lean_object* v_a_2198_ = stack[1].m_obj;
lean_object* v_a_2199_ = stack[2].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(v_x_2197_, v_a_2198_, v_a_2199_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object* v_x_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(v_x_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2220_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(lean_object* v_00_u03b1_2221_, lean_object* v_msg_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v_msg_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2222_ = stack[1].m_obj;
lean_object* v___y_2223_ = stack[2].m_obj;
lean_object* v___y_2224_ = stack[3].m_obj;
lean_object* v___y_2225_ = stack[4].m_obj;
lean_object* v___y_2226_ = stack[5].m_obj;
lean_object* v___y_2227_ = stack[6].m_obj;
lean_object* v___y_2228_ = stack[7].m_obj;
lean_object* v_res_2231_;
v_res_2231_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(lean_box(0), v_msg_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
stack->m_obj
 = v_res_2231_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_msg_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(v_00_u03b1_2232_, v_msg_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
return v_res_2241_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(lean_object* v_msgData_2242_, lean_object* v_macroStack_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_2242_, v_macroStack_2243_, v___y_2248_);
return v___x_2251_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2242_ = stack[0].m_obj;
lean_object* v_macroStack_2243_ = stack[1].m_obj;
lean_object* v___y_2244_ = stack[2].m_obj;
lean_object* v___y_2245_ = stack[3].m_obj;
lean_object* v___y_2246_ = stack[4].m_obj;
lean_object* v___y_2247_ = stack[5].m_obj;
lean_object* v___y_2248_ = stack[6].m_obj;
lean_object* v___y_2249_ = stack[7].m_obj;
lean_object* v_res_2252_;
v_res_2252_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(v_msgData_2242_, v_macroStack_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
stack->m_obj
 = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___boxed(lean_object* v_msgData_2253_, lean_object* v_macroStack_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(v_msgData_2253_, v_macroStack_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2262_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1(){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2271_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2272_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2));
v___x_2273_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1));
v___x_2274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed), 4, 0);
v___x_2275_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2271_, v___x_2272_, v___x_2273_, v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2276_;
v_res_2276_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
stack->m_obj
 = v_res_2276_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___boxed(lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
return v_res_2278_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3(){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1));
v___x_2306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6));
v___x_2307_ = l_Lean_addBuiltinDeclarationRanges(v___x_2305_, v___x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2308_;
v_res_2308_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
stack->m_obj
 = v_res_2308_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___boxed(lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
return v_res_2310_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1));
v___x_2316_ = l_Lean_mkConst(v___x_2315_, v___x_2314_);
return v___x_2316_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object* v_e_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2323_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2324_ = 1;
v___x_2325_ = 0;
v___x_2326_ = l_Lean_Meta_evalExpr___redArg(v___x_2323_, v_e_2317_, v___x_2324_, v___x_2325_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
return v___x_2326_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2317_ = stack[0].m_obj;
lean_object* v_a_2318_ = stack[1].m_obj;
lean_object* v_a_2319_ = stack[2].m_obj;
lean_object* v_a_2320_ = stack[3].m_obj;
lean_object* v_a_2321_ = stack[4].m_obj;
lean_object* v_res_2327_;
v_res_2327_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(v_e_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
stack->m_obj
 = v_res_2327_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___boxed(lean_object* v_e_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(v_e_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
return v_res_2334_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0));
v___x_2337_ = l_Lean_stringToMessageData(v___x_2336_);
return v___x_2337_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2));
v___x_2340_ = l_Lean_stringToMessageData(v___x_2339_);
return v___x_2340_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(lean_object* v___x_2341_, lean_object* v___x_2342_, uint8_t v___x_2343_, lean_object* v___x_2344_, lean_object* v___x_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2341_, v___x_2342_, v___x_2343_, v___x_2343_, v___x_2344_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = 0;
v___x_2356_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2355_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2357_; lean_object* v_a_2358_; lean_object* v___x_2359_; 
lean_dec_ref_known(v___x_2356_, 1);
v___x_2357_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_2354_, v___y_2349_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc_n(v_a_2358_, 2);
lean_dec_ref(v___x_2357_);
v___x_2359_ = l_Lean_Meta_getMVars(v_a_2358_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = lean_array_get_size(v_a_2360_);
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = lean_nat_dec_eq(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec(v_a_2358_);
lean_dec_ref(v___x_2345_);
v___x_2364_ = lean_box(0);
v___x_2365_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2360_, v___x_2364_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v_a_2360_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2373_; 
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; 
v_unused_2374_ = lean_ctor_get(v___x_2365_, 0);
lean_dec(v_unused_2374_);
v___x_2367_ = v___x_2365_;
v_isShared_2368_ = v_isSharedCheck_2373_;
goto v_resetjp_2366_;
}
else
{
lean_dec(v___x_2365_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2373_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_box(0);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2369_);
v___x_2371_ = v___x_2367_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
v_a_2375_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2365_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2365_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
uint8_t v___x_2383_; lean_object* v___x_2384_; 
lean_dec(v_a_2360_);
v___x_2383_ = 1;
lean_inc(v_a_2358_);
v___x_2384_ = l_Lean_Meta_evalExpr___redArg(v___x_2345_, v_a_2358_, v___x_2383_, v___x_2355_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2400_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2400_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2400_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
uint8_t v___x_2389_; 
v___x_2389_ = lean_unbox(v_a_2385_);
lean_dec(v_a_2385_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_del_object(v___x_2387_);
v___x_2390_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1);
v___x_2391_ = l_Lean_indentExpr(v_a_2358_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_2394_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
lean_dec(v_a_2358_);
v___x_2396_ = lean_box(0);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v___x_2396_);
v___x_2398_ = v___x_2387_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec(v_a_2358_);
v_a_2401_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2384_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2384_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_a_2358_);
lean_dec_ref(v___x_2345_);
v_a_2409_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2359_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2359_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_dec(v_a_2354_);
lean_dec_ref(v___x_2345_);
return v___x_2356_;
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec_ref(v___x_2345_);
v_a_2417_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2353_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2353_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2341_ = stack[0].m_obj;
lean_object* v___x_2342_ = stack[1].m_obj;
uint8_t v___x_2343_ = stack[2].m_num;
lean_object* v___x_2344_ = stack[3].m_obj;
lean_object* v___x_2345_ = stack[4].m_obj;
lean_object* v___y_2346_ = stack[5].m_obj;
lean_object* v___y_2347_ = stack[6].m_obj;
lean_object* v___y_2348_ = stack[7].m_obj;
lean_object* v___y_2349_ = stack[8].m_obj;
lean_object* v___y_2350_ = stack[9].m_obj;
lean_object* v___y_2351_ = stack[10].m_obj;
lean_object* v_res_2425_;
v_res_2425_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(v___x_2341_, v___x_2342_, v___x_2343_, v___x_2344_, v___x_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
stack->m_obj
 = v_res_2425_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(lean_object* v___x_2426_, lean_object* v___x_2427_, lean_object* v___x_2428_, lean_object* v___x_2429_, lean_object* v___x_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v___x_1273__boxed_2438_; lean_object* v_res_2439_; 
v___x_1273__boxed_2438_ = lean_unbox(v___x_2428_);
v_res_2439_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(v___x_2426_, v___x_2427_, v___x_1273__boxed_2438_, v___x_2429_, v___x_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
return v_res_2439_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
return v___x_2447_;
}
}
lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object* v_x_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2452_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1));
lean_inc(v_x_2448_);
v___x_2453_ = l_Lean_Syntax_isOfKind(v_x_2448_, v___x_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec(v_x_2448_);
v___x_2454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; 
v___x_2455_ = lean_unsigned_to_nat(1u);
v___x_2456_ = l_Lean_Syntax_getArg(v_x_2448_, v___x_2455_);
lean_dec(v_x_2448_);
v___x_2457_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2458_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2);
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_box(v___x_2453_);
v___f_2461_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2461_, 0, v___x_2456_);
lean_closure_set(v___f_2461_, 1, v___x_2458_);
lean_closure_set(v___f_2461_, 2, v___x_2460_);
lean_closure_set(v___f_2461_, 3, v___x_2459_);
lean_closure_set(v___f_2461_, 4, v___x_2457_);
v___x_2462_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2461_, v_a_2449_, v_a_2450_);
return v___x_2462_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2448_ = stack[0].m_obj;
lean_object* v_a_2449_ = stack[1].m_obj;
lean_object* v_a_2450_ = stack[2].m_obj;
lean_object* v_res_2463_;
v_res_2463_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(v_x_2448_, v_a_2449_, v_a_2450_);
stack->m_obj
 = v_res_2463_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object* v_x_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(v_x_2464_, v_a_2465_, v_a_2466_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
return v_res_2468_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1(){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2477_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2478_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1));
v___x_2479_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1));
v___x_2480_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed), 4, 0);
v___x_2481_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2477_, v___x_2478_, v___x_2479_, v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2482_;
v_res_2482_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
stack->m_obj
 = v_res_2482_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___boxed(lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
return v_res_2484_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3(){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1));
v___x_2512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6));
v___x_2513_ = l_Lean_addBuiltinDeclarationRanges(v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2514_;
v_res_2514_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
stack->m_obj
 = v_res_2514_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___boxed(lean_object* v_a_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
return v_res_2516_;
}
}
lean_object* runtime_initialize_Init_Guard(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Guard(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Guard(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Guard(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Guard(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Guard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Guard(builtin);
}
#ifdef __cplusplus
}
#endif
