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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 1)
{
uint8_t v_red_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_red_9_ = lean_ctor_get_uint8(v_t_7_, 0);
v___x_10_ = lean_box(v_red_9_);
v___x_11_ = lean_apply_1(v_k_8_, v___x_10_);
return v___x_11_;
}
else
{
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg___boxed(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_12_, v_k_13_);
lean_dec(v_t_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_t_23_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(lean_object* v_t_27_, lean_object* v_syntactic_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_27_, v_syntactic_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg___boxed(lean_object* v_t_30_, lean_object* v_syntactic_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(v_t_30_, v_syntactic_31_);
lean_dec(v_t_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_syntactic_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_34_, v_syntactic_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___boxed(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_syntactic_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(v_motive_38_, v_t_39_, v_h_40_, v_syntactic_41_);
lean_dec(v_t_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(lean_object* v_t_43_, lean_object* v_defEq_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_43_, v_defEq_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg___boxed(lean_object* v_t_46_, lean_object* v_defEq_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(v_t_46_, v_defEq_47_);
lean_dec(v_t_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_defEq_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_50_, v_defEq_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___boxed(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_defEq_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(v_motive_54_, v_t_55_, v_h_56_, v_defEq_57_);
lean_dec(v_t_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(lean_object* v_t_59_, lean_object* v_alphaEq_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_59_, v_alphaEq_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg___boxed(lean_object* v_t_62_, lean_object* v_alphaEq_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(v_t_62_, v_alphaEq_63_);
lean_dec(v_t_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_alphaEq_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_66_, v_alphaEq_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_alphaEq_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(v_motive_70_, v_t_71_, v_h_72_, v_alphaEq_73_);
lean_dec(v_t_71_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3));
lean_inc(v_x_114_);
v___x_116_ = l_Lean_Syntax_isOfKind(v_x_114_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
lean_dec(v_x_114_);
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_114_, v___x_118_);
lean_dec(v_x_114_);
v___x_120_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5));
lean_inc(v___x_119_);
v___x_121_ = l_Lean_Syntax_isOfKind(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7));
lean_inc(v___x_119_);
v___x_123_ = l_Lean_Syntax_isOfKind(v___x_119_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9));
lean_inc(v___x_119_);
v___x_125_ = l_Lean_Syntax_isOfKind(v___x_119_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11));
v___x_127_ = l_Lean_Syntax_isOfKind(v___x_119_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12));
return v___x_129_;
}
}
else
{
lean_object* v___x_130_; 
lean_dec(v___x_119_);
v___x_130_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13));
return v___x_130_;
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v___x_119_);
v___x_131_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15));
return v___x_131_;
}
}
else
{
lean_object* v___x_132_; 
lean_dec(v___x_119_);
v___x_132_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17));
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(lean_object* v_x_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1));
lean_inc(v_x_158_);
v___x_160_ = l_Lean_Syntax_isOfKind(v_x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec(v_x_158_);
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = l_Lean_Syntax_getArg(v_x_158_, v___x_162_);
lean_dec(v_x_158_);
v___x_164_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3));
lean_inc(v___x_163_);
v___x_165_ = l_Lean_Syntax_isOfKind(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5));
lean_inc(v___x_163_);
v___x_167_ = l_Lean_Syntax_isOfKind(v___x_163_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7));
lean_inc(v___x_163_);
v___x_169_ = l_Lean_Syntax_isOfKind(v___x_163_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9));
v___x_171_ = l_Lean_Syntax_isOfKind(v___x_163_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12));
return v___x_173_;
}
}
else
{
lean_object* v___x_174_; 
lean_dec(v___x_163_);
v___x_174_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13));
return v___x_174_;
}
}
else
{
lean_object* v___x_175_; 
lean_dec(v___x_163_);
v___x_175_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15));
return v___x_175_;
}
}
else
{
lean_object* v___x_176_; 
lean_dec(v___x_163_);
v___x_176_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17));
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(lean_object* v_x_202_){
_start:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_x_202_);
v___x_204_ = l_Lean_Syntax_isOfKind(v_x_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
lean_dec(v_x_202_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = l_Lean_Syntax_getArg(v_x_202_, v___x_206_);
lean_dec(v_x_202_);
v___x_208_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3));
lean_inc(v___x_207_);
v___x_209_ = l_Lean_Syntax_isOfKind(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5));
lean_inc(v___x_207_);
v___x_211_ = l_Lean_Syntax_isOfKind(v___x_207_, v___x_210_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7));
lean_inc(v___x_207_);
v___x_213_ = l_Lean_Syntax_isOfKind(v___x_207_, v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9));
v___x_215_ = l_Lean_Syntax_isOfKind(v___x_207_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12));
return v___x_217_;
}
}
else
{
lean_object* v___x_218_; 
lean_dec(v___x_207_);
v___x_218_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13));
return v___x_218_;
}
}
else
{
lean_object* v___x_219_; 
lean_dec(v___x_207_);
v___x_219_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15));
return v___x_219_;
}
}
else
{
lean_object* v___x_220_; 
lean_dec(v___x_207_);
v___x_220_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17));
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(lean_object* v_x_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_saveState___redArg(v___y_223_, v___y_225_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v_r_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
lean_inc(v___y_225_);
lean_inc_ref(v___y_224_);
lean_inc(v___y_223_);
lean_inc_ref(v___y_222_);
v_r_229_ = lean_apply_5(v_x_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, lean_box(0));
if (lean_obj_tag(v_r_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v_r_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v_r_229_, 1);
v___x_231_ = l_Lean_Meta_SavedState_restore___redArg(v_a_228_, v___y_223_, v___y_225_);
lean_dec(v_a_228_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v___x_231_, 0);
lean_dec(v_unused_239_);
v___x_233_ = v___x_231_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_dec(v___x_231_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v_a_230_);
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_230_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_a_230_);
v_a_240_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_231_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_231_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_249_; 
v_a_248_ = lean_ctor_get(v_r_229_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v_r_229_, 1);
v___x_249_ = l_Lean_Meta_SavedState_restore___redArg(v_a_228_, v___y_223_, v___y_225_);
lean_dec(v_a_228_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v___x_249_, 0);
lean_dec(v_unused_257_);
v___x_251_ = v___x_249_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_dec(v___x_249_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 1);
lean_ctor_set(v___x_251_, 0, v_a_248_);
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_248_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec(v_a_248_);
v_a_258_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_249_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_249_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v_x_221_);
v_a_266_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_227_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_227_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg___boxed(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(lean_object* v_00_u03b1_281_, lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
return v___x_288_;
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(uint8_t v_red_297_, lean_object* v_a_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(lean_object* v_red_347_, lean_object* v_a_348_, lean_object* v_b_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
uint8_t v_red_1706__boxed_355_; lean_object* v_res_356_; 
v_red_1706__boxed_355_ = lean_unbox(v_red_347_);
v_res_356_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(v_red_1706__boxed_355_, v_a_348_, v_b_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec(v___y_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object* v_a_357_, lean_object* v_b_358_, lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
switch(lean_obj_tag(v_x_359_))
{
case 0:
{
lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_365_ = l_Lean_Expr_consumeMData(v_a_357_);
lean_dec_ref(v_a_357_);
v___x_366_ = l_Lean_Expr_consumeMData(v_b_358_);
lean_dec_ref(v_b_358_);
v___x_367_ = lean_expr_eqv(v___x_365_, v___x_366_);
lean_dec_ref(v___x_366_);
lean_dec_ref(v___x_365_);
v___x_368_ = lean_box(v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
case 1:
{
uint8_t v_red_370_; lean_object* v___x_371_; lean_object* v___f_372_; lean_object* v___x_373_; 
v_red_370_ = lean_ctor_get_uint8(v_x_359_, 0);
v___x_371_ = lean_box(v_red_370_);
v___f_372_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_372_, 0, v___x_371_);
lean_closure_set(v___f_372_, 1, v_a_357_);
lean_closure_set(v___f_372_, 2, v_b_358_);
v___x_373_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v___f_372_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_373_;
}
default: 
{
uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_expr_eqv(v_a_357_, v_b_358_);
lean_dec_ref(v_b_358_);
lean_dec_ref(v_a_357_);
v___x_375_ = lean_box(v___x_374_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(lean_object* v_a_377_, lean_object* v_b_378_, lean_object* v_x_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_377_, v_b_378_, v_x_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_x_379_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(lean_object* v_x_394_){
_start:
{
switch(lean_obj_tag(v_x_394_))
{
case 0:
{
lean_object* v___x_395_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0));
return v___x_395_;
}
case 1:
{
uint8_t v_red_396_; 
v_red_396_ = lean_ctor_get_uint8(v_x_394_, 0);
switch(v_red_396_)
{
case 0:
{
lean_object* v___x_397_; 
v___x_397_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1));
return v___x_397_;
}
case 1:
{
lean_object* v___x_398_; 
v___x_398_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2));
return v___x_398_;
}
case 2:
{
lean_object* v___x_399_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3));
return v___x_399_;
}
case 3:
{
lean_object* v___x_400_; 
v___x_400_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4));
return v___x_400_;
}
case 4:
{
lean_object* v___x_401_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5));
return v___x_401_;
}
default: 
{
lean_object* v___x_402_; 
v___x_402_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6));
return v___x_402_;
}
}
}
default: 
{
lean_object* v___x_403_; 
v___x_403_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__7));
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___boxed(lean_object* v_x_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_x_404_);
lean_dec(v_x_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(lean_object* v_e_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = l_Lean_Expr_hasMVar(v_e_406_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_e_406_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v_mctx_412_; lean_object* v___x_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; lean_object* v_cache_417_; lean_object* v_zetaDeltaFVarIds_418_; lean_object* v_postponed_419_; lean_object* v_diag_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_429_; 
v___x_411_ = lean_st_ref_get(v___y_407_);
v_mctx_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_mctx_412_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_instantiateMVarsCore(v_mctx_412_, v_e_406_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_snd_415_);
lean_dec_ref(v___x_413_);
v___x_416_ = lean_st_ref_take(v___y_407_);
v_cache_417_ = lean_ctor_get(v___x_416_, 1);
v_zetaDeltaFVarIds_418_ = lean_ctor_get(v___x_416_, 2);
v_postponed_419_ = lean_ctor_get(v___x_416_, 3);
v_diag_420_ = lean_ctor_get(v___x_416_, 4);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v___x_416_, 0);
lean_dec(v_unused_430_);
v___x_422_ = v___x_416_;
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_diag_420_);
lean_inc(v_postponed_419_);
lean_inc(v_zetaDeltaFVarIds_418_);
lean_inc(v_cache_417_);
lean_dec(v___x_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_snd_415_);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_snd_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_cache_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_zetaDeltaFVarIds_418_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_postponed_419_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_diag_420_);
v___x_425_ = v_reuseFailAlloc_428_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_st_ref_put(v___y_407_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v_fst_414_);
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(lean_object* v_e_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_431_, v___y_432_);
lean_dec(v___y_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_435_, v___y_439_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(lean_object* v_e_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(v_e_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(lean_object* v_a_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg___boxed(lean_object* v_a_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(v_a_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(lean_object* v_00_u03b1_471_, lean_object* v_a_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___boxed(lean_object* v_00_u03b1_481_, lean_object* v_a_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(v_00_u03b1_481_, v_a_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(lean_object* v_a_491_, lean_object* v___x_492_, uint8_t v___x_493_, lean_object* v_b_494_, lean_object* v_mk_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
lean_inc(v___x_492_);
v___x_503_ = l_Lean_Elab_Term_elabTerm(v_a_491_, v___x_492_, v___x_493_, v___x_493_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = l_Lean_Elab_Term_elabTerm(v_b_494_, v___x_492_, v___x_493_, v___x_493_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v_a_504_);
v___x_507_ = lean_infer_type(v_a_504_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v_a_506_);
v___x_509_ = lean_infer_type(v_a_506_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Meta_isExprDefEqGuarded(v_a_508_, v_a_510_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_511_) == 0)
{
uint8_t v___x_512_; lean_object* v___x_513_; 
lean_dec_ref_known(v___x_511_, 1);
v___x_512_ = 0;
v___x_513_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_512_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_516_; lean_object* v_a_517_; lean_object* v___x_518_; 
lean_dec_ref_known(v___x_513_, 1);
v___x_514_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_504_, v___y_499_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v___x_516_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_506_, v___y_499_);
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref(v___x_516_);
v___x_518_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_515_, v_a_517_, v_mk_495_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v___x_518_;
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_506_);
lean_dec(v_a_504_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
v_a_519_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_513_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_513_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_dec(v_a_506_);
lean_dec(v_a_504_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v___x_511_;
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_a_508_);
lean_dec(v_a_506_);
lean_dec(v_a_504_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
v_a_527_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_509_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_509_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_506_);
lean_dec(v_a_504_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
v_a_535_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_507_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_507_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_a_504_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
v_a_543_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_505_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_505_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v_b_494_);
lean_dec(v___x_492_);
v_a_551_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_503_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_503_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed(lean_object* v_a_559_, lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v_b_562_, lean_object* v_mk_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
uint8_t v___x_1761__boxed_571_; lean_object* v_res_572_; 
v___x_1761__boxed_571_ = lean_unbox(v___x_561_);
v_res_572_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(v_a_559_, v___x_560_, v___x_1761__boxed_571_, v_b_562_, v_mk_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v_mk_563_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object* v_mk_573_, lean_object* v_a_574_, lean_object* v_b_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v___f_586_; lean_object* v___x_587_; 
v___x_583_ = lean_box(0);
v___x_584_ = 1;
v___x_585_ = lean_box(v___x_584_);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed), 12, 5);
lean_closure_set(v___f_586_, 0, v_a_574_);
lean_closure_set(v___f_586_, 1, v___x_583_);
lean_closure_set(v___f_586_, 2, v___x_585_);
lean_closure_set(v___f_586_, 3, v_b_575_);
lean_closure_set(v___f_586_, 4, v_mk_573_);
v___x_587_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_586_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___boxed(lean_object* v_mk_588_, lean_object* v_a_589_, lean_object* v_b_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_mk_588_, v_a_589_, v_b_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v___x_600_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___boxed(lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(lean_object* v_00_u03b1_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___boxed(lean_object* v_00_u03b1_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(v_00_u03b1_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(lean_object* v_msgData_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; lean_object* v_env_636_; lean_object* v___x_637_; lean_object* v_toCold_638_; lean_object* v_mctx_639_; lean_object* v_lctx_640_; lean_object* v_options_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_635_ = lean_st_ref_get(v___y_633_);
v_env_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc_ref(v_env_636_);
lean_dec(v___x_635_);
v___x_637_ = lean_st_ref_get(v___y_631_);
v_toCold_638_ = lean_ctor_get(v___y_632_, 0);
v_mctx_639_ = lean_ctor_get(v___x_637_, 0);
lean_inc_ref(v_mctx_639_);
lean_dec(v___x_637_);
v_lctx_640_ = lean_ctor_get(v___y_630_, 2);
v_options_641_ = lean_ctor_get(v_toCold_638_, 2);
lean_inc_ref(v_options_641_);
lean_inc_ref(v_lctx_640_);
v___x_642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_642_, 0, v_env_636_);
lean_ctor_set(v___x_642_, 1, v_mctx_639_);
lean_ctor_set(v___x_642_, 2, v_lctx_640_);
lean_ctor_set(v___x_642_, 3, v_options_641_);
v___x_643_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_msgData_629_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1___boxed(lean_object* v_msgData_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msgData_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_ref_658_; lean_object* v___x_659_; lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_ref_658_ = lean_ctor_get(v___y_655_, 2);
v___x_659_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_668_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
lean_inc(v_ref_658_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_ref_658_);
lean_ctor_set(v___x_664_, 1, v_a_660_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 1);
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg___boxed(lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v_msg_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_675_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2));
v___x_681_ = l_Lean_stringToMessageData(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(lean_object* v___x_688_, lean_object* v_r_689_, lean_object* v_p_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
if (lean_obj_tag(v___x_688_) == 1)
{
lean_object* v_val_700_; lean_object* v___x_701_; 
v_val_700_ = lean_ctor_get(v___x_688_, 0);
lean_inc_n(v_val_700_, 2);
lean_dec_ref_known(v___x_688_, 1);
lean_inc(v_p_690_);
lean_inc(v_r_689_);
v___x_701_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_val_700_, v_r_689_, v_p_690_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_726_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_726_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_726_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v___x_706_; 
v___x_706_ = lean_unbox(v_a_702_);
lean_dec(v_a_702_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
lean_del_object(v___x_704_);
v___x_707_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1);
v___x_708_ = l_Lean_MessageData_ofSyntax(v_r_689_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_700_);
lean_dec(v_val_700_);
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_711_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_714_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v___x_717_ = l_Lean_MessageData_ofSyntax(v_p_690_);
v___x_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_720_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_724_; 
lean_dec(v_val_700_);
lean_dec(v_p_690_);
lean_dec(v_r_689_);
v___x_722_ = lean_box(0);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_722_);
v___x_724_ = v___x_704_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_val_700_);
lean_dec(v_p_690_);
lean_dec(v_r_689_);
v_a_727_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_701_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_701_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v___x_735_; 
lean_dec(v_p_690_);
lean_dec(v_r_689_);
lean_dec(v___x_688_);
v___x_735_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed(lean_object* v___x_736_, lean_object* v_r_737_, lean_object* v_p_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(v___x_736_, v_r_737_, v_p_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object* v_x_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2));
lean_inc(v_x_762_);
v___x_773_ = l_Lean_Syntax_isOfKind(v_x_762_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4));
lean_inc(v_x_762_);
v___x_775_ = l_Lean_Syntax_isOfKind(v_x_762_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec(v_x_762_);
v___x_776_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_776_;
}
else
{
lean_object* v___x_777_; lean_object* v_r_778_; lean_object* v___x_779_; lean_object* v_eq_780_; 
v___x_777_ = lean_unsigned_to_nat(1u);
v_r_778_ = l_Lean_Syntax_getArg(v_x_762_, v___x_777_);
v___x_779_ = lean_unsigned_to_nat(2u);
v_eq_780_ = l_Lean_Syntax_getArg(v_x_762_, v___x_779_);
if (v___x_773_ == 0)
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_780_);
v___x_788_ = l_Lean_Syntax_isOfKind(v_eq_780_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v_eq_780_);
lean_dec(v_r_778_);
lean_dec(v_x_762_);
v___x_789_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_789_;
}
else
{
goto v___jp_781_;
}
}
else
{
goto v___jp_781_;
}
v___jp_781_:
{
lean_object* v___x_782_; lean_object* v_p_783_; lean_object* v___x_784_; lean_object* v___y_785_; lean_object* v___x_786_; 
v___x_782_ = lean_unsigned_to_nat(3u);
v_p_783_ = l_Lean_Syntax_getArg(v_x_762_, v___x_782_);
lean_dec(v_x_762_);
v___x_784_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_780_);
v___y_785_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 12, 3);
lean_closure_set(v___y_785_, 0, v___x_784_);
lean_closure_set(v___y_785_, 1, v_r_778_);
lean_closure_set(v___y_785_, 2, v_p_783_);
v___x_786_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_785_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
return v___x_786_;
}
}
}
else
{
lean_object* v___x_790_; lean_object* v_eq_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_790_ = lean_unsigned_to_nat(2u);
v_eq_791_ = l_Lean_Syntax_getArg(v_x_762_, v___x_790_);
v___x_792_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_791_);
v___x_793_ = l_Lean_Syntax_isOfKind(v_eq_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
lean_dec(v_eq_791_);
lean_dec(v_x_762_);
v___x_794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v_r_796_; lean_object* v___x_797_; lean_object* v_p_798_; lean_object* v___x_799_; lean_object* v___y_800_; lean_object* v___x_801_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v_r_796_ = l_Lean_Syntax_getArg(v_x_762_, v___x_795_);
v___x_797_ = lean_unsigned_to_nat(3u);
v_p_798_ = l_Lean_Syntax_getArg(v_x_762_, v___x_797_);
lean_dec(v_x_762_);
v___x_799_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_791_);
v___y_800_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 12, 3);
lean_closure_set(v___y_800_, 0, v___x_799_);
lean_closure_set(v___y_800_, 1, v_r_796_);
lean_closure_set(v___y_800_, 2, v_p_798_);
v___x_801_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_800_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed(lean_object* v_x_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(v_x_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(lean_object* v_00_u03b1_813_, lean_object* v_msg_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v_msg_814_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___boxed(lean_object* v_00_u03b1_825_, lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(v_00_u03b1_825_, v_msg_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1(){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_847_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_848_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2));
v___x_849_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3));
v___x_850_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed), 10, 0);
v___x_851_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_847_, v___x_848_, v___x_849_, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___boxed(lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3(){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3));
v___x_881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6));
v___x_882_ = l_Lean_addBuiltinDeclarationRanges(v___x_880_, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___boxed(lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1(){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___f_915_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed), 10, 0);
v___x_916_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_917_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4));
v___x_918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1));
v___x_919_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_916_, v___x_917_, v___x_918_, v___f_915_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___boxed(lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3(){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1));
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6));
v___x_950_ = l_Lean_addBuiltinDeclarationRanges(v___x_948_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___boxed(lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(lean_object* v_e_953_, lean_object* v___y_954_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_Expr_hasMVar(v_e_953_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v_e_953_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v_mctx_959_; lean_object* v___x_960_; lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v___x_963_; lean_object* v_cache_964_; lean_object* v_zetaDeltaFVarIds_965_; lean_object* v_postponed_966_; lean_object* v_diag_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_976_; 
v___x_958_ = lean_st_ref_get(v___y_954_);
v_mctx_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc_ref(v_mctx_959_);
lean_dec(v___x_958_);
v___x_960_ = l_Lean_instantiateMVarsCore(v_mctx_959_, v_e_953_);
v_fst_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_fst_961_);
v_snd_962_ = lean_ctor_get(v___x_960_, 1);
lean_inc(v_snd_962_);
lean_dec_ref(v___x_960_);
v___x_963_ = lean_st_ref_take(v___y_954_);
v_cache_964_ = lean_ctor_get(v___x_963_, 1);
v_zetaDeltaFVarIds_965_ = lean_ctor_get(v___x_963_, 2);
v_postponed_966_ = lean_ctor_get(v___x_963_, 3);
v_diag_967_ = lean_ctor_get(v___x_963_, 4);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_977_);
v___x_969_ = v___x_963_;
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_diag_967_);
lean_inc(v_postponed_966_);
lean_inc(v_zetaDeltaFVarIds_965_);
lean_inc(v_cache_964_);
lean_dec(v___x_963_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_snd_962_);
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_snd_962_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_cache_964_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_zetaDeltaFVarIds_965_);
lean_ctor_set(v_reuseFailAlloc_975_, 3, v_postponed_966_);
lean_ctor_set(v_reuseFailAlloc_975_, 4, v_diag_967_);
v___x_972_ = v_reuseFailAlloc_975_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_st_ref_put(v___y_954_, v___x_972_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_fst_961_);
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg___boxed(lean_object* v_e_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_978_, v___y_979_);
lean_dec(v___y_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(lean_object* v_e_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_982_, v___y_988_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___boxed(lean_object* v_e_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(v_e_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_1003_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0));
v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2));
v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(lean_object* v_getTgt_1010_, lean_object* v_r_1011_, lean_object* v_eq_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
v___x_1022_ = lean_apply_9(v_getTgt_1010_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1083_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v___x_1024_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_a_1023_, v___y_1018_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1083_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1083_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; 
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v_a_1025_);
v___x_1029_ = lean_infer_type(v_a_1025_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 1);
lean_ctor_set(v___x_1027_, 0, v_a_1030_);
v___x_1032_ = v___x_1027_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1030_);
v___x_1032_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
uint8_t v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = 0;
v___x_1034_ = l_Lean_Elab_Tactic_elabTerm(v_r_1011_, v___x_1032_, v___x_1033_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_1012_);
if (lean_obj_tag(v___x_1036_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; 
v_val_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v___x_1036_, 1);
lean_inc(v_a_1025_);
lean_inc(v_a_1035_);
v___x_1038_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1035_, v_a_1025_, v_val_1037_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v_val_1037_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1056_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1056_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1056_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_unbox(v_a_1039_);
lean_dec(v_a_1039_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
lean_del_object(v___x_1041_);
v___x_1044_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1);
v___x_1045_ = l_Lean_indentExpr(v_a_1025_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_indentExpr(v_a_1035_);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1050_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1054_; 
lean_dec(v_a_1035_);
lean_dec(v_a_1025_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
v___x_1052_ = lean_box(0);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1052_);
v___x_1054_ = v___x_1041_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
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
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_a_1035_);
lean_dec(v_a_1025_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
v_a_1057_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1038_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1038_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v___x_1065_; 
lean_dec(v___x_1036_);
lean_dec(v_a_1035_);
lean_dec(v_a_1025_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
v___x_1065_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1065_;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec(v_a_1025_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v_eq_1012_);
v_a_1066_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1034_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1034_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
lean_del_object(v___x_1027_);
lean_dec(v_a_1025_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v_eq_1012_);
lean_dec(v_r_1011_);
v_a_1075_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1029_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1029_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v_eq_1012_);
lean_dec(v_r_1011_);
v_a_1084_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1022_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1022_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed(lean_object* v_getTgt_1092_, lean_object* v_r_1093_, lean_object* v_eq_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(v_getTgt_1092_, v_r_1093_, v_eq_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object* v_x_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_eq_1130_; lean_object* v_r_1131_; lean_object* v_getTgt_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1));
lean_inc(v_x_1119_);
v___x_1144_ = l_Lean_Syntax_isOfKind(v_x_1119_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3));
lean_inc(v_x_1119_);
v___x_1146_ = l_Lean_Syntax_isOfKind(v_x_1119_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec(v_x_1119_);
v___x_1147_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1147_;
}
else
{
lean_object* v___x_1148_; lean_object* v_eq_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1148_ = lean_unsigned_to_nat(1u);
v_eq_1149_ = l_Lean_Syntax_getArg(v_x_1119_, v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(2u);
v___x_1151_ = l_Lean_Syntax_getArg(v_x_1119_, v___x_1150_);
lean_dec(v_x_1119_);
v___x_1152_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4));
v_eq_1130_ = v_eq_1149_;
v_r_1131_ = v___x_1151_;
v_getTgt_1132_ = v___x_1152_;
v___y_1133_ = v_a_1120_;
v___y_1134_ = v_a_1121_;
v___y_1135_ = v_a_1122_;
v___y_1136_ = v_a_1123_;
v___y_1137_ = v_a_1124_;
v___y_1138_ = v_a_1125_;
v___y_1139_ = v_a_1126_;
v___y_1140_ = v_a_1127_;
goto v___jp_1129_;
}
}
else
{
lean_object* v___x_1153_; lean_object* v_eq_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v_eq_1154_ = l_Lean_Syntax_getArg(v_x_1119_, v___x_1153_);
v___x_1155_ = lean_unsigned_to_nat(2u);
v___x_1156_ = l_Lean_Syntax_getArg(v_x_1119_, v___x_1155_);
lean_dec(v_x_1119_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5));
v_eq_1130_ = v_eq_1154_;
v_r_1131_ = v___x_1156_;
v_getTgt_1132_ = v___x_1157_;
v___y_1133_ = v_a_1120_;
v___y_1134_ = v_a_1121_;
v___y_1135_ = v_a_1122_;
v___y_1136_ = v_a_1123_;
v___y_1137_ = v_a_1124_;
v___y_1138_ = v_a_1125_;
v___y_1139_ = v_a_1126_;
v___y_1140_ = v_a_1127_;
goto v___jp_1129_;
}
v___jp_1129_:
{
lean_object* v___f_1141_; lean_object* v___x_1142_; 
lean_inc_ref(v_getTgt_1132_);
v___f_1141_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1141_, 0, v_getTgt_1132_);
lean_closure_set(v___f_1141_, 1, v_r_1131_);
lean_closure_set(v___f_1141_, 2, v_eq_1130_);
v___x_1142_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1141_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed(lean_object* v_x_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(v_x_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1(){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1177_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1178_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1));
v___x_1179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1));
v___x_1180_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed), 10, 0);
v___x_1181_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1177_, v___x_1178_, v___x_1179_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___boxed(lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3(){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1));
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6));
v___x_1212_ = l_Lean_addBuiltinDeclarationRanges(v___x_1210_, v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___boxed(lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1(){
_start:
{
lean_object* v___f_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed), 10, 0);
v___x_1246_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1247_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3));
v___x_1248_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1));
v___x_1249_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1246_, v___x_1247_, v___x_1248_, v___f_1245_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___boxed(lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3(){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1));
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6));
v___x_1280_ = l_Lean_addBuiltinDeclarationRanges(v___x_1278_, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___boxed(lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
return v_res_1282_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(lean_object* v___x_1307_, uint8_t v___x_1308_, lean_object* v_val_1309_, lean_object* v_eq_1310_, lean_object* v_c_1311_, lean_object* v_ty_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v_lDecl_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___x_1457_; 
lean_inc(v___x_1307_);
v___x_1457_ = l_Lean_Elab_Tactic_getFVarId(v___x_1307_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v_lctx_1459_; lean_object* v___x_1460_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v_lctx_1459_ = lean_ctor_get(v___y_1317_, 2);
lean_inc_ref(v_lctx_1459_);
v___x_1460_ = lean_local_ctx_find(v_lctx_1459_, v_a_1458_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_ty_1312_);
lean_dec(v_c_1311_);
lean_dec(v_eq_1310_);
lean_dec(v_val_1309_);
v___x_1461_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1462_ = l_Lean_MessageData_ofSyntax(v___x_1307_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1465_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v___y_1317_);
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_val_1475_; 
v_val_1475_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1475_);
lean_dec_ref_known(v___x_1460_, 1);
v_lDecl_1406_ = v_val_1475_;
v___y_1407_ = v___y_1313_;
v___y_1408_ = v___y_1314_;
v___y_1409_ = v___y_1315_;
v___y_1410_ = v___y_1316_;
v___y_1411_ = v___y_1317_;
v___y_1412_ = v___y_1318_;
v___y_1413_ = v___y_1319_;
v___y_1414_ = v___y_1320_;
goto v___jp_1405_;
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v___y_1317_);
lean_dec(v_ty_1312_);
lean_dec(v_c_1311_);
lean_dec(v_eq_1310_);
lean_dec(v_val_1309_);
lean_dec(v___x_1307_);
v_a_1476_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1457_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1457_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
v___jp_1322_:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_LocalDecl_value_x3f(v___y_1323_, v___x_1308_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_dec_ref(v___y_1323_);
lean_dec(v_eq_1310_);
if (lean_obj_tag(v_val_1309_) == 0)
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v___y_1328_);
lean_dec(v___x_1307_);
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
return v___x_1334_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_dec_ref_known(v_val_1309_, 1);
v___x_1335_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1336_ = l_Lean_MessageData_ofSyntax(v___x_1307_);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1339_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec_ref(v___y_1328_);
return v___x_1340_;
}
}
else
{
if (lean_obj_tag(v_val_1309_) == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec_ref_known(v___x_1332_, 1);
lean_dec_ref(v___y_1323_);
lean_dec(v_eq_1310_);
v___x_1341_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1342_ = l_Lean_MessageData_ofSyntax(v___x_1307_);
v___x_1343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1345_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec_ref(v___y_1328_);
return v___x_1346_;
}
else
{
if (lean_obj_tag(v_eq_1310_) == 0)
{
lean_object* v___x_1347_; 
lean_dec_ref_known(v_val_1309_, 1);
lean_dec_ref_known(v___x_1332_, 1);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v___y_1323_);
lean_dec(v___x_1307_);
v___x_1347_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1347_;
}
else
{
lean_object* v_val_1348_; lean_object* v_val_1349_; lean_object* v_val_1350_; lean_object* v___x_1351_; 
v_val_1348_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v___x_1332_, 1);
v_val_1349_ = lean_ctor_get(v_val_1309_, 0);
lean_inc(v_val_1349_);
lean_dec_ref_known(v_val_1309_, 1);
v_val_1350_ = lean_ctor_get(v_eq_1310_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v_eq_1310_, 1);
v___x_1351_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_1350_);
if (lean_obj_tag(v___x_1351_) == 1)
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1403_; 
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1403_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1403_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = l_Lean_LocalDecl_type(v___y_1323_);
lean_dec_ref(v___y_1323_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Elab_Tactic_elabTerm(v_val_1349_, v___x_1358_, v___x_1308_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; lean_object* v_a_1362_; lean_object* v___x_1363_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_n(v_a_1360_, 2);
lean_dec_ref_known(v___x_1359_, 1);
v___x_1361_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_1348_, v___y_1329_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc_n(v_a_1362_, 2);
lean_dec_ref(v___x_1361_);
v___x_1363_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1360_, v_a_1362_, v_val_1352_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v_val_1352_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1385_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1385_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1385_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_unbox(v_a_1364_);
lean_dec(v_a_1364_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_del_object(v___x_1366_);
v___x_1369_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1370_ = l_Lean_MessageData_ofSyntax(v___x_1307_);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_indentExpr(v_a_1362_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_indentExpr(v_a_1360_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1379_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec_ref(v___y_1328_);
return v___x_1380_;
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec(v_a_1362_);
lean_dec(v_a_1360_);
lean_dec_ref(v___y_1328_);
lean_dec(v___x_1307_);
v___x_1381_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1381_);
v___x_1383_ = v___x_1366_;
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
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_a_1362_);
lean_dec(v_a_1360_);
lean_dec_ref(v___y_1328_);
lean_dec(v___x_1307_);
v_a_1386_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1363_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1363_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_val_1352_);
lean_dec(v_val_1348_);
lean_dec_ref(v___y_1328_);
lean_dec(v___x_1307_);
v_a_1394_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1359_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1359_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
else
{
lean_object* v___x_1404_; 
lean_dec(v___x_1351_);
lean_dec(v_val_1349_);
lean_dec(v_val_1348_);
lean_dec_ref(v___y_1328_);
lean_dec_ref(v___y_1323_);
lean_dec(v___x_1307_);
v___x_1404_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1404_;
}
}
}
}
}
v___jp_1405_:
{
if (lean_obj_tag(v_c_1311_) == 1)
{
if (lean_obj_tag(v_ty_1312_) == 1)
{
lean_object* v_val_1415_; lean_object* v_val_1416_; lean_object* v___x_1417_; 
v_val_1415_ = lean_ctor_get(v_c_1311_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v_c_1311_, 1);
v_val_1416_ = lean_ctor_get(v_ty_1312_, 0);
lean_inc(v_val_1416_);
lean_dec_ref_known(v_ty_1312_, 1);
v___x_1417_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_1415_);
if (lean_obj_tag(v___x_1417_) == 1)
{
lean_object* v_val_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v_val_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Lean_Elab_Tactic_elabTerm(v_val_1416_, v___x_1419_, v___x_1308_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc_n(v_a_1421_, 2);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_Lean_LocalDecl_type(v_lDecl_1406_);
v___x_1423_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_1422_, v___y_1412_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc_n(v_a_1424_, 2);
lean_dec_ref(v___x_1423_);
v___x_1425_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1421_, v_a_1424_, v_val_1418_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v_val_1418_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; uint8_t v___x_1427_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = lean_unbox(v_a_1426_);
lean_dec(v_a_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
lean_dec_ref(v_lDecl_1406_);
lean_dec(v_eq_1310_);
lean_dec(v_val_1309_);
v___x_1428_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1429_ = l_Lean_MessageData_ofSyntax(v___x_1307_);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l_Lean_indentExpr(v_a_1424_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = l_Lean_indentExpr(v_a_1421_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1438_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec_ref(v___y_1411_);
return v___x_1439_;
}
else
{
lean_dec(v_a_1424_);
lean_dec(v_a_1421_);
v___y_1323_ = v_lDecl_1406_;
v___y_1324_ = v___y_1407_;
v___y_1325_ = v___y_1408_;
v___y_1326_ = v___y_1409_;
v___y_1327_ = v___y_1410_;
v___y_1328_ = v___y_1411_;
v___y_1329_ = v___y_1412_;
v___y_1330_ = v___y_1413_;
v___y_1331_ = v___y_1414_;
goto v___jp_1322_;
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_a_1424_);
lean_dec(v_a_1421_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_lDecl_1406_);
lean_dec(v_eq_1310_);
lean_dec(v_val_1309_);
lean_dec(v___x_1307_);
v_a_1440_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1425_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1425_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_val_1418_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_lDecl_1406_);
lean_dec(v_eq_1310_);
lean_dec(v_val_1309_);
lean_dec(v___x_1307_);
v_a_1448_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1420_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1420_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v___x_1456_; 
lean_dec(v___x_1417_);
lean_dec(v_val_1416_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_lDecl_1406_);
lean_dec(v_eq_1310_);
lean_dec(v_val_1309_);
lean_dec(v___x_1307_);
v___x_1456_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1456_;
}
}
else
{
lean_dec_ref_known(v_c_1311_, 1);
lean_dec(v_ty_1312_);
v___y_1323_ = v_lDecl_1406_;
v___y_1324_ = v___y_1407_;
v___y_1325_ = v___y_1408_;
v___y_1326_ = v___y_1409_;
v___y_1327_ = v___y_1410_;
v___y_1328_ = v___y_1411_;
v___y_1329_ = v___y_1412_;
v___y_1330_ = v___y_1413_;
v___y_1331_ = v___y_1414_;
goto v___jp_1322_;
}
}
else
{
lean_dec(v_ty_1312_);
lean_dec(v_c_1311_);
v___y_1323_ = v_lDecl_1406_;
v___y_1324_ = v___y_1407_;
v___y_1325_ = v___y_1408_;
v___y_1326_ = v___y_1409_;
v___y_1327_ = v___y_1410_;
v___y_1328_ = v___y_1411_;
v___y_1329_ = v___y_1412_;
v___y_1330_ = v___y_1413_;
v___y_1331_ = v___y_1414_;
goto v___jp_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed(lean_object* v___x_1484_, lean_object* v___x_1485_, lean_object* v_val_1486_, lean_object* v_eq_1487_, lean_object* v_c_1488_, lean_object* v_ty_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
uint8_t v___x_8219__boxed_1499_; lean_object* v_res_1500_; 
v___x_8219__boxed_1499_ = lean_unbox(v___x_1485_);
v_res_1500_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(v___x_1484_, v___x_8219__boxed_1499_, v_val_1486_, v_eq_1487_, v_c_1488_, v_ty_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(lean_object* v___x_1501_, lean_object* v_val_1502_, lean_object* v_eq_1503_, lean_object* v_c_1504_, lean_object* v_ty_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v_lDecl_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; lean_object* v___x_1652_; 
lean_inc(v___x_1501_);
v___x_1652_ = l_Lean_Elab_Tactic_getFVarId(v___x_1501_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v_lctx_1654_; lean_object* v___x_1655_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v___x_1652_, 1);
v_lctx_1654_ = lean_ctor_get(v___y_1510_, 2);
lean_inc_ref(v_lctx_1654_);
v___x_1655_ = lean_local_ctx_find(v_lctx_1654_, v_a_1653_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_dec(v_ty_1505_);
lean_dec(v_c_1504_);
lean_dec(v_eq_1503_);
lean_dec(v_val_1502_);
v___x_1656_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1657_ = l_Lean_MessageData_ofSyntax(v___x_1501_);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1660_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec_ref(v___y_1510_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_val_1670_; 
v_val_1670_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v___x_1655_, 1);
v_lDecl_1600_ = v_val_1670_;
v___y_1601_ = v___y_1506_;
v___y_1602_ = v___y_1507_;
v___y_1603_ = v___y_1508_;
v___y_1604_ = v___y_1509_;
v___y_1605_ = v___y_1510_;
v___y_1606_ = v___y_1511_;
v___y_1607_ = v___y_1512_;
v___y_1608_ = v___y_1513_;
goto v___jp_1599_;
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec_ref(v___y_1510_);
lean_dec(v_ty_1505_);
lean_dec(v_c_1504_);
lean_dec(v_eq_1503_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
v_a_1671_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1652_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1652_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
v___jp_1515_:
{
uint8_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = 0;
v___x_1526_ = l_Lean_LocalDecl_value_x3f(v___y_1516_, v___x_1525_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_dec_ref(v___y_1516_);
lean_dec(v_eq_1503_);
if (lean_obj_tag(v_val_1502_) == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec_ref(v___y_1521_);
lean_dec(v___x_1501_);
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec_ref_known(v_val_1502_, 1);
v___x_1529_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1530_ = l_Lean_MessageData_ofSyntax(v___x_1501_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1533_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec_ref(v___y_1521_);
return v___x_1534_;
}
}
else
{
if (lean_obj_tag(v_val_1502_) == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec_ref_known(v___x_1526_, 1);
lean_dec_ref(v___y_1516_);
lean_dec(v_eq_1503_);
v___x_1535_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1536_ = l_Lean_MessageData_ofSyntax(v___x_1501_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1535_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1537_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1539_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec_ref(v___y_1521_);
return v___x_1540_;
}
else
{
if (lean_obj_tag(v_eq_1503_) == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref_known(v_val_1502_, 1);
lean_dec_ref_known(v___x_1526_, 1);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v___y_1516_);
lean_dec(v___x_1501_);
v___x_1541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1541_;
}
else
{
lean_object* v_val_1542_; lean_object* v_val_1543_; lean_object* v_val_1544_; lean_object* v___x_1545_; 
v_val_1542_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v___x_1526_, 1);
v_val_1543_ = lean_ctor_get(v_val_1502_, 0);
lean_inc(v_val_1543_);
lean_dec_ref_known(v_val_1502_, 1);
v_val_1544_ = lean_ctor_get(v_eq_1503_, 0);
lean_inc(v_val_1544_);
lean_dec_ref_known(v_eq_1503_, 1);
v___x_1545_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_1544_);
if (lean_obj_tag(v___x_1545_) == 1)
{
lean_object* v_val_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1597_; 
v_val_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1597_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_val_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1597_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = l_Lean_LocalDecl_type(v___y_1516_);
lean_dec_ref(v___y_1516_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Elab_Tactic_elabTerm(v_val_1543_, v___x_1552_, v___x_1525_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc_n(v_a_1554_, 2);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_1542_, v___y_1522_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc_n(v_a_1556_, 2);
lean_dec_ref(v___x_1555_);
v___x_1557_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1554_, v_a_1556_, v_val_1546_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v_val_1546_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1579_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1579_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1579_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_unbox(v_a_1558_);
lean_dec(v_a_1558_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_del_object(v___x_1560_);
v___x_1563_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1564_ = l_Lean_MessageData_ofSyntax(v___x_1501_);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = l_Lean_indentExpr(v_a_1556_);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_indentExpr(v_a_1554_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1573_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec_ref(v___y_1521_);
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
lean_dec(v_a_1556_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1521_);
lean_dec(v___x_1501_);
v___x_1575_ = lean_box(0);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1575_);
v___x_1577_ = v___x_1560_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1556_);
lean_dec(v_a_1554_);
lean_dec_ref(v___y_1521_);
lean_dec(v___x_1501_);
v_a_1580_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1557_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1557_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec(v_val_1546_);
lean_dec(v_val_1542_);
lean_dec_ref(v___y_1521_);
lean_dec(v___x_1501_);
v_a_1588_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1553_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1553_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
else
{
lean_object* v___x_1598_; 
lean_dec(v___x_1545_);
lean_dec(v_val_1543_);
lean_dec(v_val_1542_);
lean_dec_ref(v___y_1521_);
lean_dec_ref(v___y_1516_);
lean_dec(v___x_1501_);
v___x_1598_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1598_;
}
}
}
}
}
v___jp_1599_:
{
if (lean_obj_tag(v_c_1504_) == 1)
{
if (lean_obj_tag(v_ty_1505_) == 1)
{
lean_object* v_val_1609_; lean_object* v_val_1610_; lean_object* v___x_1611_; 
v_val_1609_ = lean_ctor_get(v_c_1504_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v_c_1504_, 1);
v_val_1610_ = lean_ctor_get(v_ty_1505_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_ty_1505_, 1);
v___x_1611_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_1609_);
if (lean_obj_tag(v___x_1611_) == 1)
{
lean_object* v_val_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; lean_object* v___x_1615_; 
v_val_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = lean_box(0);
v___x_1614_ = 0;
v___x_1615_ = l_Lean_Elab_Tactic_elabTerm(v_val_1610_, v___x_1613_, v___x_1614_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_a_1619_; lean_object* v___x_1620_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc_n(v_a_1616_, 2);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_LocalDecl_type(v_lDecl_1600_);
v___x_1618_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_1617_, v___y_1606_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc_n(v_a_1619_, 2);
lean_dec_ref(v___x_1618_);
v___x_1620_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1616_, v_a_1619_, v_val_1612_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v_val_1612_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; uint8_t v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = lean_unbox(v_a_1621_);
lean_dec(v_a_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref(v_lDecl_1600_);
lean_dec(v_eq_1503_);
lean_dec(v_val_1502_);
v___x_1623_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1624_ = l_Lean_MessageData_ofSyntax(v___x_1501_);
v___x_1625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1623_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
v___x_1626_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l_Lean_indentExpr(v_a_1619_);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_indentExpr(v_a_1616_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1633_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec_ref(v___y_1605_);
return v___x_1634_;
}
else
{
lean_dec(v_a_1619_);
lean_dec(v_a_1616_);
v___y_1516_ = v_lDecl_1600_;
v___y_1517_ = v___y_1601_;
v___y_1518_ = v___y_1602_;
v___y_1519_ = v___y_1603_;
v___y_1520_ = v___y_1604_;
v___y_1521_ = v___y_1605_;
v___y_1522_ = v___y_1606_;
v___y_1523_ = v___y_1607_;
v___y_1524_ = v___y_1608_;
goto v___jp_1515_;
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_dec(v_a_1619_);
lean_dec(v_a_1616_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_lDecl_1600_);
lean_dec(v_eq_1503_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
v_a_1635_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1620_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1620_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec(v_val_1612_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_lDecl_1600_);
lean_dec(v_eq_1503_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
v_a_1643_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1615_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1615_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v___x_1651_; 
lean_dec(v___x_1611_);
lean_dec(v_val_1610_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_lDecl_1600_);
lean_dec(v_eq_1503_);
lean_dec(v_val_1502_);
lean_dec(v___x_1501_);
v___x_1651_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1651_;
}
}
else
{
lean_dec_ref_known(v_c_1504_, 1);
lean_dec(v_ty_1505_);
v___y_1516_ = v_lDecl_1600_;
v___y_1517_ = v___y_1601_;
v___y_1518_ = v___y_1602_;
v___y_1519_ = v___y_1603_;
v___y_1520_ = v___y_1604_;
v___y_1521_ = v___y_1605_;
v___y_1522_ = v___y_1606_;
v___y_1523_ = v___y_1607_;
v___y_1524_ = v___y_1608_;
goto v___jp_1515_;
}
}
else
{
lean_dec(v_ty_1505_);
lean_dec(v_c_1504_);
v___y_1516_ = v_lDecl_1600_;
v___y_1517_ = v___y_1601_;
v___y_1518_ = v___y_1602_;
v___y_1519_ = v___y_1603_;
v___y_1520_ = v___y_1604_;
v___y_1521_ = v___y_1605_;
v___y_1522_ = v___y_1606_;
v___y_1523_ = v___y_1607_;
v___y_1524_ = v___y_1608_;
goto v___jp_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed(lean_object* v___x_1679_, lean_object* v_val_1680_, lean_object* v_eq_1681_, lean_object* v_c_1682_, lean_object* v_ty_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(v___x_1679_, v_val_1680_, v_eq_1681_, v_c_1682_, v_ty_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object* v_x_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1));
lean_inc(v_x_1706_);
v___x_1717_ = l_Lean_Syntax_isOfKind(v_x_1706_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3));
lean_inc(v_x_1706_);
v___x_1719_ = l_Lean_Syntax_isOfKind(v_x_1706_, v___x_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec(v_x_1706_);
v___x_1720_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1720_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v_eq_1735_; lean_object* v_val_1736_; lean_object* v___x_1740_; lean_object* v_c_1742_; lean_object* v_ty_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_unsigned_to_nat(1u);
v___x_1723_ = l_Lean_Syntax_getArg(v_x_1706_, v___x_1722_);
v___x_1740_ = lean_unsigned_to_nat(2u);
v___x_1762_ = l_Lean_Syntax_getArg(v_x_1706_, v___x_1740_);
v___x_1763_ = l_Lean_Syntax_isNone(v___x_1762_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; 
lean_inc(v___x_1762_);
v___x_1764_ = l_Lean_Syntax_matchesNull(v___x_1762_, v___x_1740_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_dec(v___x_1762_);
lean_dec(v___x_1723_);
lean_dec(v_x_1706_);
v___x_1765_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1765_;
}
else
{
lean_object* v_c_1766_; lean_object* v_ty_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_c_1766_ = l_Lean_Syntax_getArg(v___x_1762_, v___x_1721_);
v_ty_1767_ = l_Lean_Syntax_getArg(v___x_1762_, v___x_1722_);
lean_dec(v___x_1762_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_c_1766_);
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v_ty_1767_);
v_c_1742_ = v___x_1768_;
v_ty_1743_ = v___x_1769_;
v___y_1744_ = v_a_1707_;
v___y_1745_ = v_a_1708_;
v___y_1746_ = v_a_1709_;
v___y_1747_ = v_a_1710_;
v___y_1748_ = v_a_1711_;
v___y_1749_ = v_a_1712_;
v___y_1750_ = v_a_1713_;
v___y_1751_ = v_a_1714_;
goto v___jp_1741_;
}
}
else
{
lean_object* v___x_1770_; 
lean_dec(v___x_1762_);
v___x_1770_ = lean_box(0);
v_c_1742_ = v___x_1770_;
v_ty_1743_ = v___x_1770_;
v___y_1744_ = v_a_1707_;
v___y_1745_ = v_a_1708_;
v___y_1746_ = v_a_1709_;
v___y_1747_ = v_a_1710_;
v___y_1748_ = v_a_1711_;
v___y_1749_ = v_a_1712_;
v___y_1750_ = v_a_1713_;
v___y_1751_ = v_a_1714_;
goto v___jp_1741_;
}
v___jp_1724_:
{
lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_box(v___x_1717_);
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed), 15, 6);
lean_closure_set(v___f_1738_, 0, v___x_1723_);
lean_closure_set(v___f_1738_, 1, v___x_1737_);
lean_closure_set(v___f_1738_, 2, v_val_1736_);
lean_closure_set(v___f_1738_, 3, v_eq_1735_);
lean_closure_set(v___f_1738_, 4, v___y_1729_);
lean_closure_set(v___f_1738_, 5, v___y_1730_);
v___x_1739_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1738_, v___y_1733_, v___y_1732_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1734_, v___y_1728_, v___y_1731_);
return v___x_1739_;
}
v___jp_1741_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = lean_unsigned_to_nat(3u);
v___x_1753_ = l_Lean_Syntax_getArg(v_x_1706_, v___x_1752_);
lean_dec(v_x_1706_);
v___x_1754_ = l_Lean_Syntax_isNone(v___x_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
lean_inc(v___x_1753_);
v___x_1755_ = l_Lean_Syntax_matchesNull(v___x_1753_, v___x_1740_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_dec(v___x_1753_);
lean_dec(v_ty_1743_);
lean_dec(v_c_1742_);
lean_dec(v___x_1723_);
v___x_1756_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1756_;
}
else
{
lean_object* v_eq_1757_; lean_object* v_val_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_eq_1757_ = l_Lean_Syntax_getArg(v___x_1753_, v___x_1721_);
v_val_1758_ = l_Lean_Syntax_getArg(v___x_1753_, v___x_1722_);
lean_dec(v___x_1753_);
v___x_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1759_, 0, v_eq_1757_);
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_val_1758_);
v___y_1725_ = v___y_1746_;
v___y_1726_ = v___y_1747_;
v___y_1727_ = v___y_1748_;
v___y_1728_ = v___y_1750_;
v___y_1729_ = v_c_1742_;
v___y_1730_ = v_ty_1743_;
v___y_1731_ = v___y_1751_;
v___y_1732_ = v___y_1745_;
v___y_1733_ = v___y_1744_;
v___y_1734_ = v___y_1749_;
v_eq_1735_ = v___x_1759_;
v_val_1736_ = v___x_1760_;
goto v___jp_1724_;
}
}
else
{
lean_object* v___x_1761_; 
lean_dec(v___x_1753_);
v___x_1761_ = lean_box(0);
v___y_1725_ = v___y_1746_;
v___y_1726_ = v___y_1747_;
v___y_1727_ = v___y_1748_;
v___y_1728_ = v___y_1750_;
v___y_1729_ = v_c_1742_;
v___y_1730_ = v_ty_1743_;
v___y_1731_ = v___y_1751_;
v___y_1732_ = v___y_1745_;
v___y_1733_ = v___y_1744_;
v___y_1734_ = v___y_1749_;
v_eq_1735_ = v___x_1761_;
v_val_1736_ = v___x_1761_;
goto v___jp_1724_;
}
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v_eq_1785_; lean_object* v_val_1786_; lean_object* v___x_1789_; lean_object* v_c_1791_; lean_object* v_ty_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = l_Lean_Syntax_getArg(v_x_1706_, v___x_1772_);
v___x_1789_ = lean_unsigned_to_nat(2u);
v___x_1811_ = l_Lean_Syntax_getArg(v_x_1706_, v___x_1789_);
v___x_1812_ = l_Lean_Syntax_isNone(v___x_1811_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; 
lean_inc(v___x_1811_);
v___x_1813_ = l_Lean_Syntax_matchesNull(v___x_1811_, v___x_1789_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
lean_dec(v___x_1811_);
lean_dec(v___x_1773_);
lean_dec(v_x_1706_);
v___x_1814_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1814_;
}
else
{
lean_object* v_c_1815_; lean_object* v_ty_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_c_1815_ = l_Lean_Syntax_getArg(v___x_1811_, v___x_1771_);
v_ty_1816_ = l_Lean_Syntax_getArg(v___x_1811_, v___x_1772_);
lean_dec(v___x_1811_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_c_1815_);
v___x_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_ty_1816_);
v_c_1791_ = v___x_1817_;
v_ty_1792_ = v___x_1818_;
v___y_1793_ = v_a_1707_;
v___y_1794_ = v_a_1708_;
v___y_1795_ = v_a_1709_;
v___y_1796_ = v_a_1710_;
v___y_1797_ = v_a_1711_;
v___y_1798_ = v_a_1712_;
v___y_1799_ = v_a_1713_;
v___y_1800_ = v_a_1714_;
goto v___jp_1790_;
}
}
else
{
lean_object* v___x_1819_; 
lean_dec(v___x_1811_);
v___x_1819_ = lean_box(0);
v_c_1791_ = v___x_1819_;
v_ty_1792_ = v___x_1819_;
v___y_1793_ = v_a_1707_;
v___y_1794_ = v_a_1708_;
v___y_1795_ = v_a_1709_;
v___y_1796_ = v_a_1710_;
v___y_1797_ = v_a_1711_;
v___y_1798_ = v_a_1712_;
v___y_1799_ = v_a_1713_;
v___y_1800_ = v_a_1714_;
goto v___jp_1790_;
}
v___jp_1774_:
{
lean_object* v___f_1787_; lean_object* v___x_1788_; 
v___f_1787_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1787_, 0, v___x_1773_);
lean_closure_set(v___f_1787_, 1, v_val_1786_);
lean_closure_set(v___f_1787_, 2, v_eq_1785_);
lean_closure_set(v___f_1787_, 3, v___y_1779_);
lean_closure_set(v___f_1787_, 4, v___y_1783_);
v___x_1788_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1787_, v___y_1777_, v___y_1782_, v___y_1784_, v___y_1781_, v___y_1778_, v___y_1780_, v___y_1775_, v___y_1776_);
return v___x_1788_;
}
v___jp_1790_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_unsigned_to_nat(3u);
v___x_1802_ = l_Lean_Syntax_getArg(v_x_1706_, v___x_1801_);
lean_dec(v_x_1706_);
v___x_1803_ = l_Lean_Syntax_isNone(v___x_1802_);
if (v___x_1803_ == 0)
{
uint8_t v___x_1804_; 
lean_inc(v___x_1802_);
v___x_1804_ = l_Lean_Syntax_matchesNull(v___x_1802_, v___x_1789_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_dec(v___x_1802_);
lean_dec(v_ty_1792_);
lean_dec(v_c_1791_);
lean_dec(v___x_1773_);
v___x_1805_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1805_;
}
else
{
lean_object* v_eq_1806_; lean_object* v_val_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_eq_1806_ = l_Lean_Syntax_getArg(v___x_1802_, v___x_1771_);
v_val_1807_ = l_Lean_Syntax_getArg(v___x_1802_, v___x_1772_);
lean_dec(v___x_1802_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_eq_1806_);
v___x_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_val_1807_);
v___y_1775_ = v___y_1799_;
v___y_1776_ = v___y_1800_;
v___y_1777_ = v___y_1793_;
v___y_1778_ = v___y_1797_;
v___y_1779_ = v_c_1791_;
v___y_1780_ = v___y_1798_;
v___y_1781_ = v___y_1796_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v_ty_1792_;
v___y_1784_ = v___y_1795_;
v_eq_1785_ = v___x_1808_;
v_val_1786_ = v___x_1809_;
goto v___jp_1774_;
}
}
else
{
lean_object* v___x_1810_; 
lean_dec(v___x_1802_);
v___x_1810_ = lean_box(0);
v___y_1775_ = v___y_1799_;
v___y_1776_ = v___y_1800_;
v___y_1777_ = v___y_1793_;
v___y_1778_ = v___y_1797_;
v___y_1779_ = v_c_1791_;
v___y_1780_ = v___y_1798_;
v___y_1781_ = v___y_1796_;
v___y_1782_ = v___y_1794_;
v___y_1783_ = v_ty_1792_;
v___y_1784_ = v___y_1795_;
v_eq_1785_ = v___x_1810_;
v_val_1786_ = v___x_1810_;
goto v___jp_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed(lean_object* v_x_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(v_x_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1(){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1839_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1));
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1));
v___x_1842_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed), 10, 0);
v___x_1843_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1839_, v___x_1840_, v___x_1841_, v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___boxed(lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3(){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1));
v___x_1873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6));
v___x_1874_ = l_Lean_addBuiltinDeclarationRanges(v___x_1872_, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___boxed(lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1(){
_start:
{
lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed), 10, 0);
v___x_1908_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1909_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3));
v___x_1910_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1));
v___x_1911_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1908_, v___x_1909_, v___x_1910_, v___f_1907_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___boxed(lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3(){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1));
v___x_1941_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6));
v___x_1942_ = l_Lean_addBuiltinDeclarationRanges(v___x_1940_, v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___boxed(lean_object* v_a_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg___boxed(lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(lean_object* v_00_u03b1_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___boxed(lean_object* v_00_u03b1_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(v_00_u03b1_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg(){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg___boxed(lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(lean_object* v_00_u03b1_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___boxed(lean_object* v_00_u03b1_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(v_00_u03b1_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1982_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(lean_object* v_opts_1983_, lean_object* v_opt_1984_){
_start:
{
lean_object* v_name_1985_; lean_object* v_defValue_1986_; lean_object* v_map_1987_; lean_object* v___x_1988_; 
v_name_1985_ = lean_ctor_get(v_opt_1984_, 0);
v_defValue_1986_ = lean_ctor_get(v_opt_1984_, 1);
v_map_1987_ = lean_ctor_get(v_opts_1983_, 0);
v___x_1988_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1987_, v_name_1985_);
if (lean_obj_tag(v___x_1988_) == 0)
{
uint8_t v___x_1989_; 
v___x_1989_ = lean_unbox(v_defValue_1986_);
return v___x_1989_;
}
else
{
lean_object* v_val_1990_; 
v_val_1990_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v___x_1988_, 1);
if (lean_obj_tag(v_val_1990_) == 1)
{
uint8_t v_v_1991_; 
v_v_1991_ = lean_ctor_get_uint8(v_val_1990_, 0);
lean_dec_ref_known(v_val_1990_, 0);
return v_v_1991_;
}
else
{
uint8_t v___x_1992_; 
lean_dec(v_val_1990_);
v___x_1992_ = lean_unbox(v_defValue_1986_);
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_1993_, lean_object* v_opt_1994_){
_start:
{
uint8_t v_res_1995_; lean_object* v_r_1996_; 
v_res_1995_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_opts_1993_, v_opt_1994_);
lean_dec_ref(v_opt_1994_);
lean_dec_ref(v_opts_1993_);
v_r_1996_ = lean_box(v_res_1995_);
return v_r_1996_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(1);
v___x_1998_ = l_Lean_MessageData_ofFormat(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2));
v___x_2003_ = l_Lean_MessageData_ofFormat(v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(lean_object* v_x_2004_, lean_object* v_x_2005_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 0)
{
return v_x_2004_;
}
else
{
lean_object* v_head_2006_; lean_object* v_tail_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2029_; 
v_head_2006_ = lean_ctor_get(v_x_2005_, 0);
v_tail_2007_ = lean_ctor_get(v_x_2005_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_x_2005_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2009_ = v_x_2005_;
v_isShared_2010_ = v_isSharedCheck_2029_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_tail_2007_);
lean_inc(v_head_2006_);
lean_dec(v_x_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2029_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_before_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2027_; 
v_before_2011_ = lean_ctor_get(v_head_2006_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_head_2006_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v_head_2006_, 1);
lean_dec(v_unused_2028_);
v___x_2013_ = v_head_2006_;
v_isShared_2014_ = v_isSharedCheck_2027_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_before_2011_);
lean_dec(v_head_2006_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2027_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 7);
lean_ctor_set(v___x_2013_, 1, v___x_2015_);
lean_ctor_set(v___x_2013_, 0, v_x_2004_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_x_2004_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3);
if (v_isShared_2010_ == 0)
{
lean_ctor_set_tag(v___x_2009_, 7);
lean_ctor_set(v___x_2009_, 1, v___x_2018_);
lean_ctor_set(v___x_2009_, 0, v___x_2017_);
v___x_2020_ = v___x_2009_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = l_Lean_MessageData_ofSyntax(v_before_2011_);
v___x_2022_ = l_Lean_indentD(v___x_2021_);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2020_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v_x_2004_ = v___x_2023_;
v_x_2005_ = v_tail_2007_;
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
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1));
v___x_2034_ = l_Lean_MessageData_ofFormat(v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(lean_object* v_msgData_2035_, lean_object* v_macroStack_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_toCold_2039_; lean_object* v_options_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_toCold_2039_ = lean_ctor_get(v___y_2037_, 0);
v_options_2040_ = lean_ctor_get(v_toCold_2039_, 2);
v___x_2041_ = l_Lean_Elab_pp_macroStack;
v___x_2042_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_options_2040_, v___x_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; 
lean_dec(v_macroStack_2036_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_msgData_2035_);
return v___x_2043_;
}
else
{
if (lean_obj_tag(v_macroStack_2036_) == 0)
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_msgData_2035_);
return v___x_2044_;
}
else
{
lean_object* v_head_2045_; lean_object* v_after_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2061_; 
v_head_2045_ = lean_ctor_get(v_macroStack_2036_, 0);
lean_inc(v_head_2045_);
v_after_2046_ = lean_ctor_get(v_head_2045_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_head_2045_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_head_2045_, 0);
lean_dec(v_unused_2062_);
v___x_2048_ = v_head_2045_;
v_isShared_2049_ = v_isSharedCheck_2061_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_after_2046_);
lean_dec(v_head_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2061_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 7);
lean_ctor_set(v___x_2048_, 1, v___x_2050_);
lean_ctor_set(v___x_2048_, 0, v_msgData_2035_);
v___x_2052_ = v___x_2048_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_msgData_2035_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v_msgData_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2053_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = l_Lean_MessageData_ofSyntax(v_after_2046_);
v___x_2056_ = l_Lean_indentD(v___x_2055_);
v_msgData_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2057_, 0, v___x_2054_);
lean_ctor_set(v_msgData_2057_, 1, v___x_2056_);
v___x_2058_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(v_msgData_2057_, v_macroStack_2036_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2063_, lean_object* v_macroStack_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_2063_, v_macroStack_2064_, v___y_2065_);
lean_dec_ref(v___y_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(lean_object* v_msg_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_ref_2076_; lean_object* v___x_2077_; lean_object* v_a_2078_; lean_object* v_macroStack_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
v_ref_2076_ = lean_ctor_get(v___y_2073_, 2);
v___x_2077_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_2068_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
v_macroStack_2079_ = lean_ctor_get(v___y_2069_, 1);
v___x_2080_ = l_Lean_Elab_getBetterRef(v_ref_2076_, v_macroStack_2079_);
lean_inc(v_macroStack_2079_);
v___x_2081_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_a_2078_, v_macroStack_2079_, v___y_2073_);
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2080_);
lean_ctor_set(v___x_2086_, 1, v_a_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 1);
lean_ctor_set(v___x_2084_, 0, v___x_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg___boxed(lean_object* v_msg_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v_msg_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(lean_object* v_eq_2100_, lean_object* v_r_2101_, lean_object* v_p_2102_, lean_object* v_x_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_2100_);
if (lean_obj_tag(v___x_2111_) == 1)
{
lean_object* v_val_2112_; lean_object* v___x_2113_; 
v_val_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_n(v_val_2112_, 2);
lean_dec_ref_known(v___x_2111_, 1);
lean_inc(v_p_2102_);
lean_inc(v_r_2101_);
v___x_2113_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_val_2112_, v_r_2101_, v_p_2102_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2138_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2138_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2138_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_unbox(v_a_2114_);
lean_dec(v_a_2114_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_del_object(v___x_2116_);
v___x_2119_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1);
v___x_2120_ = l_Lean_MessageData_ofSyntax(v_r_2101_);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_2112_);
lean_dec(v_val_2112_);
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2123_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = l_Lean_MessageData_ofSyntax(v_p_2102_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_2132_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
lean_dec(v_val_2112_);
lean_dec(v_p_2102_);
lean_dec(v_r_2101_);
v___x_2134_ = lean_box(0);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2134_);
v___x_2136_ = v___x_2116_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_val_2112_);
lean_dec(v_p_2102_);
lean_dec(v_r_2101_);
v_a_2139_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2113_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2113_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v___x_2147_; 
lean_dec(v___x_2111_);
lean_dec(v_p_2102_);
lean_dec(v_r_2101_);
v___x_2147_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v___x_2147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed(lean_object* v_eq_2148_, lean_object* v_r_2149_, lean_object* v_p_2150_, lean_object* v_x_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(v_eq_2148_, v_r_2149_, v_p_2150_, v_x_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v_x_2151_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object* v_x_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2));
lean_inc(v_x_2167_);
v___x_2172_ = l_Lean_Syntax_isOfKind(v_x_2167_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
lean_dec(v_x_2167_);
v___x_2173_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; lean_object* v_eq_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2174_ = lean_unsigned_to_nat(2u);
v_eq_2175_ = l_Lean_Syntax_getArg(v_x_2167_, v___x_2174_);
v___x_2176_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_2175_);
v___x_2177_ = l_Lean_Syntax_isOfKind(v_eq_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_dec(v_eq_2175_);
lean_dec(v_x_2167_);
v___x_2178_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2178_;
}
else
{
lean_object* v___x_2179_; lean_object* v_r_2180_; lean_object* v___x_2181_; lean_object* v_p_2182_; lean_object* v___f_2183_; lean_object* v___x_2184_; 
v___x_2179_ = lean_unsigned_to_nat(1u);
v_r_2180_ = l_Lean_Syntax_getArg(v_x_2167_, v___x_2179_);
v___x_2181_ = lean_unsigned_to_nat(3u);
v_p_2182_ = l_Lean_Syntax_getArg(v_x_2167_, v___x_2181_);
lean_dec(v_x_2167_);
v___f_2183_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2183_, 0, v_eq_2175_);
lean_closure_set(v___f_2183_, 1, v_r_2180_);
lean_closure_set(v___f_2183_, 2, v_p_2182_);
v___x_2184_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_2183_, v_a_2168_, v_a_2169_);
return v___x_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object* v_x_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(v_x_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(lean_object* v_00_u03b1_2190_, lean_object* v_msg_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v_msg_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_msg_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(v_00_u03b1_2200_, v_msg_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(lean_object* v_msgData_2210_, lean_object* v_macroStack_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_2210_, v_macroStack_2211_, v___y_2216_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___boxed(lean_object* v_msgData_2220_, lean_object* v_macroStack_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(v_msgData_2220_, v_macroStack_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1(){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2238_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2239_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2));
v___x_2240_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1));
v___x_2241_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed), 4, 0);
v___x_2242_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2238_, v___x_2239_, v___x_2240_, v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___boxed(lean_object* v_a_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3(){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1));
v___x_2272_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6));
v___x_2273_ = l_Lean_addBuiltinDeclarationRanges(v___x_2271_, v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___boxed(lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
return v_res_2275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1));
v___x_2281_ = l_Lean_mkConst(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object* v_e_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; uint8_t v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2288_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2289_ = 1;
v___x_2290_ = 0;
v___x_2291_ = l_Lean_Meta_evalExpr___redArg(v___x_2288_, v_e_2282_, v___x_2289_, v___x_2290_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___boxed(lean_object* v_e_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(v_e_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0));
v___x_2301_ = l_Lean_stringToMessageData(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2));
v___x_2304_ = l_Lean_stringToMessageData(v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(lean_object* v___x_2305_, lean_object* v___x_2306_, uint8_t v___x_2307_, lean_object* v___x_2308_, lean_object* v___x_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2305_, v___x_2306_, v___x_2307_, v___x_2307_, v___x_2308_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = 0;
v___x_2320_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2319_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v___x_2321_; lean_object* v_a_2322_; lean_object* v___x_2323_; 
lean_dec_ref_known(v___x_2320_, 1);
v___x_2321_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_2318_, v___y_2313_);
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc_n(v_a_2322_, 2);
lean_dec_ref(v___x_2321_);
v___x_2323_ = l_Lean_Meta_getMVars(v_a_2322_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = lean_array_get_size(v_a_2324_);
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = lean_nat_dec_eq(v___x_2325_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_dec(v_a_2322_);
lean_dec_ref(v___x_2309_);
v___x_2328_ = lean_box(0);
v___x_2329_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2324_, v___x_2328_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v_a_2324_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2337_; 
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2337_ == 0)
{
lean_object* v_unused_2338_; 
v_unused_2338_ = lean_ctor_get(v___x_2329_, 0);
lean_dec(v_unused_2338_);
v___x_2331_ = v___x_2329_;
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
else
{
lean_dec(v___x_2329_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_box(0);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
v_a_2339_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2329_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2329_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
uint8_t v___x_2347_; lean_object* v___x_2348_; 
lean_dec(v_a_2324_);
v___x_2347_ = 1;
lean_inc(v_a_2322_);
v___x_2348_ = l_Lean_Meta_evalExpr___redArg(v___x_2309_, v_a_2322_, v___x_2347_, v___x_2319_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2364_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2364_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2364_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_unbox(v_a_2349_);
lean_dec(v_a_2349_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_del_object(v___x_2351_);
v___x_2354_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1);
v___x_2355_ = l_Lean_indentExpr(v_a_2322_);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_2358_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2359_;
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
lean_dec(v_a_2322_);
v___x_2360_ = lean_box(0);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2360_);
v___x_2362_ = v___x_2351_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
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
lean_dec(v_a_2322_);
v_a_2365_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2348_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2348_);
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
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2322_);
lean_dec_ref(v___x_2309_);
v_a_2373_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2323_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2323_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_dec(v_a_2318_);
lean_dec_ref(v___x_2309_);
return v___x_2320_;
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v___x_2309_);
v_a_2381_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2317_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2317_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(lean_object* v___x_2389_, lean_object* v___x_2390_, lean_object* v___x_2391_, lean_object* v___x_2392_, lean_object* v___x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
uint8_t v___x_1232__boxed_2401_; lean_object* v_res_2402_; 
v___x_1232__boxed_2401_ = lean_unbox(v___x_2391_);
v_res_2402_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(v___x_2389_, v___x_2390_, v___x_1232__boxed_2401_, v___x_2392_, v___x_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2402_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object* v_x_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
v___x_2415_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1));
lean_inc(v_x_2411_);
v___x_2416_ = l_Lean_Syntax_isOfKind(v_x_2411_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
lean_dec(v_x_2411_);
v___x_2417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___f_2424_; lean_object* v___x_2425_; 
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = l_Lean_Syntax_getArg(v_x_2411_, v___x_2418_);
lean_dec(v_x_2411_);
v___x_2420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2421_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2);
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_box(v___x_2416_);
v___f_2424_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed), 12, 5);
lean_closure_set(v___f_2424_, 0, v___x_2419_);
lean_closure_set(v___f_2424_, 1, v___x_2421_);
lean_closure_set(v___f_2424_, 2, v___x_2423_);
lean_closure_set(v___f_2424_, 3, v___x_2422_);
lean_closure_set(v___f_2424_, 4, v___x_2420_);
v___x_2425_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2424_, v_a_2412_, v_a_2413_);
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object* v_x_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(v_x_2426_, v_a_2427_, v_a_2428_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1(){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2439_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2440_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1));
v___x_2441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1));
v___x_2442_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed), 4, 0);
v___x_2443_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2439_, v___x_2440_, v___x_2441_, v___x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___boxed(lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3(){
_start:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1));
v___x_2473_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6));
v___x_2474_ = l_Lean_addBuiltinDeclarationRanges(v___x_2472_, v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___boxed(lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
return v_res_2476_;
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
