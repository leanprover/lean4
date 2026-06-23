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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_305_; uint8_t v_foApprox_306_; uint8_t v_ctxApprox_307_; uint8_t v_quasiPatternApprox_308_; uint8_t v_constApprox_309_; uint8_t v_isDefEqStuckEx_310_; uint8_t v_unificationHints_311_; uint8_t v_proofIrrelevance_312_; uint8_t v_assignSyntheticOpaque_313_; uint8_t v_offsetCnstrs_314_; uint8_t v_etaStruct_315_; uint8_t v_univApprox_316_; uint8_t v_iota_317_; uint8_t v_beta_318_; uint8_t v_proj_319_; uint8_t v_zeta_320_; uint8_t v_zetaDelta_321_; uint8_t v_zetaUnused_322_; uint8_t v_zetaHave_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_362_; 
v___x_305_ = l_Lean_Meta_Context_config(v___y_300_);
v_foApprox_306_ = lean_ctor_get_uint8(v___x_305_, 0);
v_ctxApprox_307_ = lean_ctor_get_uint8(v___x_305_, 1);
v_quasiPatternApprox_308_ = lean_ctor_get_uint8(v___x_305_, 2);
v_constApprox_309_ = lean_ctor_get_uint8(v___x_305_, 3);
v_isDefEqStuckEx_310_ = lean_ctor_get_uint8(v___x_305_, 4);
v_unificationHints_311_ = lean_ctor_get_uint8(v___x_305_, 5);
v_proofIrrelevance_312_ = lean_ctor_get_uint8(v___x_305_, 6);
v_assignSyntheticOpaque_313_ = lean_ctor_get_uint8(v___x_305_, 7);
v_offsetCnstrs_314_ = lean_ctor_get_uint8(v___x_305_, 8);
v_etaStruct_315_ = lean_ctor_get_uint8(v___x_305_, 10);
v_univApprox_316_ = lean_ctor_get_uint8(v___x_305_, 11);
v_iota_317_ = lean_ctor_get_uint8(v___x_305_, 12);
v_beta_318_ = lean_ctor_get_uint8(v___x_305_, 13);
v_proj_319_ = lean_ctor_get_uint8(v___x_305_, 14);
v_zeta_320_ = lean_ctor_get_uint8(v___x_305_, 15);
v_zetaDelta_321_ = lean_ctor_get_uint8(v___x_305_, 16);
v_zetaUnused_322_ = lean_ctor_get_uint8(v___x_305_, 17);
v_zetaHave_323_ = lean_ctor_get_uint8(v___x_305_, 18);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_362_ == 0)
{
v___x_325_ = v___x_305_;
v_isShared_326_ = v_isSharedCheck_362_;
goto v_resetjp_324_;
}
else
{
lean_dec(v___x_305_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_362_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
uint8_t v_trackZetaDelta_327_; lean_object* v_zetaDeltaSet_328_; lean_object* v_lctx_329_; lean_object* v_localInstances_330_; lean_object* v_defEqCtx_x3f_331_; lean_object* v_synthPendingDepth_332_; lean_object* v_canUnfold_x3f_333_; uint8_t v_univApprox_334_; uint8_t v_inTypeClassResolution_335_; uint8_t v_cacheInferType_336_; lean_object* v_config_338_; 
v_trackZetaDelta_327_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7);
v_zetaDeltaSet_328_ = lean_ctor_get(v___y_300_, 1);
lean_inc(v_zetaDeltaSet_328_);
v_lctx_329_ = lean_ctor_get(v___y_300_, 2);
lean_inc_ref(v_lctx_329_);
v_localInstances_330_ = lean_ctor_get(v___y_300_, 3);
lean_inc_ref(v_localInstances_330_);
v_defEqCtx_x3f_331_ = lean_ctor_get(v___y_300_, 4);
lean_inc(v_defEqCtx_x3f_331_);
v_synthPendingDepth_332_ = lean_ctor_get(v___y_300_, 5);
lean_inc(v_synthPendingDepth_332_);
v_canUnfold_x3f_333_ = lean_ctor_get(v___y_300_, 6);
lean_inc(v_canUnfold_x3f_333_);
v_univApprox_334_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_335_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7 + 2);
v_cacheInferType_336_ = lean_ctor_get_uint8(v___y_300_, sizeof(void*)*7 + 3);
if (v_isShared_326_ == 0)
{
v_config_338_ = v___x_325_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 0, v_foApprox_306_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 1, v_ctxApprox_307_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 2, v_quasiPatternApprox_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 3, v_constApprox_309_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 4, v_isDefEqStuckEx_310_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 5, v_unificationHints_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 6, v_proofIrrelevance_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 7, v_assignSyntheticOpaque_313_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 8, v_offsetCnstrs_314_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 10, v_etaStruct_315_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 11, v_univApprox_316_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 12, v_iota_317_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 13, v_beta_318_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 14, v_proj_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 15, v_zeta_320_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 16, v_zetaDelta_321_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 17, v_zetaUnused_322_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, 18, v_zetaHave_323_);
v_config_338_ = v_reuseFailAlloc_361_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
uint64_t v___x_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_353_; 
lean_ctor_set_uint8(v_config_338_, 9, v_red_297_);
v___x_339_ = l_Lean_Meta_Context_configKey(v___y_300_);
v_isSharedCheck_353_ = !lean_is_exclusive(v___y_300_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; lean_object* v_unused_358_; lean_object* v_unused_359_; lean_object* v_unused_360_; 
v_unused_354_ = lean_ctor_get(v___y_300_, 6);
lean_dec(v_unused_354_);
v_unused_355_ = lean_ctor_get(v___y_300_, 5);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v___y_300_, 4);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v___y_300_, 3);
lean_dec(v_unused_357_);
v_unused_358_ = lean_ctor_get(v___y_300_, 2);
lean_dec(v_unused_358_);
v_unused_359_ = lean_ctor_get(v___y_300_, 1);
lean_dec(v_unused_359_);
v_unused_360_ = lean_ctor_get(v___y_300_, 0);
lean_dec(v_unused_360_);
v___x_341_ = v___y_300_;
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
else
{
lean_dec(v___y_300_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_353_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v_key_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_343_ = 3ULL;
v___x_344_ = lean_uint64_shift_right(v___x_339_, v___x_343_);
v___x_345_ = lean_uint64_shift_left(v___x_344_, v___x_343_);
v___x_346_ = l_Lean_Meta_TransparencyMode_toUInt64(v_red_297_);
v_key_347_ = lean_uint64_lor(v___x_345_, v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_348_, 0, v_config_338_);
lean_ctor_set_uint64(v___x_348_, sizeof(void*)*1, v_key_347_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_348_);
v___x_350_ = v___x_341_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_zetaDeltaSet_328_);
lean_ctor_set(v_reuseFailAlloc_352_, 2, v_lctx_329_);
lean_ctor_set(v_reuseFailAlloc_352_, 3, v_localInstances_330_);
lean_ctor_set(v_reuseFailAlloc_352_, 4, v_defEqCtx_x3f_331_);
lean_ctor_set(v_reuseFailAlloc_352_, 5, v_synthPendingDepth_332_);
lean_ctor_set(v_reuseFailAlloc_352_, 6, v_canUnfold_x3f_333_);
lean_ctor_set_uint8(v_reuseFailAlloc_352_, sizeof(void*)*7, v_trackZetaDelta_327_);
lean_ctor_set_uint8(v_reuseFailAlloc_352_, sizeof(void*)*7 + 1, v_univApprox_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_352_, sizeof(void*)*7 + 2, v_inTypeClassResolution_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_352_, sizeof(void*)*7 + 3, v_cacheInferType_336_);
v___x_350_ = v_reuseFailAlloc_352_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_isExprDefEqGuarded(v_a_298_, v_b_299_, v___x_350_, v___y_301_, v___y_302_, v___y_303_);
lean_dec_ref(v___x_350_);
return v___x_351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(lean_object* v_red_363_, lean_object* v_a_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
uint8_t v_red_1784__boxed_371_; lean_object* v_res_372_; 
v_red_1784__boxed_371_ = lean_unbox(v_red_363_);
v_res_372_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(v_red_1784__boxed_371_, v_a_364_, v_b_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(lean_object* v_a_373_, lean_object* v_b_374_, lean_object* v_x_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
switch(lean_obj_tag(v_x_375_))
{
case 0:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_381_ = l_Lean_Expr_consumeMData(v_a_373_);
lean_dec_ref(v_a_373_);
v___x_382_ = l_Lean_Expr_consumeMData(v_b_374_);
lean_dec_ref(v_b_374_);
v___x_383_ = lean_expr_eqv(v___x_381_, v___x_382_);
lean_dec_ref(v___x_382_);
lean_dec_ref(v___x_381_);
v___x_384_ = lean_box(v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
case 1:
{
uint8_t v_red_386_; lean_object* v___x_387_; lean_object* v___f_388_; lean_object* v___x_389_; 
v_red_386_ = lean_ctor_get_uint8(v_x_375_, 0);
v___x_387_ = lean_box(v_red_386_);
v___f_388_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_388_, 0, v___x_387_);
lean_closure_set(v___f_388_, 1, v_a_373_);
lean_closure_set(v___f_388_, 2, v_b_374_);
v___x_389_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v___f_388_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
return v___x_389_;
}
default: 
{
uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_390_ = lean_expr_eqv(v_a_373_, v_b_374_);
lean_dec_ref(v_b_374_);
lean_dec_ref(v_a_373_);
v___x_391_ = lean_box(v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(lean_object* v_a_393_, lean_object* v_b_394_, lean_object* v_x_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_393_, v_b_394_, v_x_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_x_395_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(lean_object* v_x_410_){
_start:
{
switch(lean_obj_tag(v_x_410_))
{
case 0:
{
lean_object* v___x_411_; 
v___x_411_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0));
return v___x_411_;
}
case 1:
{
uint8_t v_red_412_; 
v_red_412_ = lean_ctor_get_uint8(v_x_410_, 0);
switch(v_red_412_)
{
case 0:
{
lean_object* v___x_413_; 
v___x_413_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1));
return v___x_413_;
}
case 1:
{
lean_object* v___x_414_; 
v___x_414_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2));
return v___x_414_;
}
case 2:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3));
return v___x_415_;
}
case 3:
{
lean_object* v___x_416_; 
v___x_416_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4));
return v___x_416_;
}
case 4:
{
lean_object* v___x_417_; 
v___x_417_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5));
return v___x_417_;
}
default: 
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6));
return v___x_418_;
}
}
}
default: 
{
lean_object* v___x_419_; 
v___x_419_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__7));
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___boxed(lean_object* v_x_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_x_420_);
lean_dec(v_x_420_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(lean_object* v_e_422_, lean_object* v___y_423_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Lean_Expr_hasMVar(v_e_422_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v_e_422_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v_mctx_428_; lean_object* v___x_429_; lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v_cache_433_; lean_object* v_zetaDeltaFVarIds_434_; lean_object* v_postponed_435_; lean_object* v_diag_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_445_; 
v___x_427_ = lean_st_ref_get(v___y_423_);
v_mctx_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_mctx_428_);
lean_dec(v___x_427_);
v___x_429_ = l_Lean_instantiateMVarsCore(v_mctx_428_, v_e_422_);
v_fst_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_fst_430_);
v_snd_431_ = lean_ctor_get(v___x_429_, 1);
lean_inc(v_snd_431_);
lean_dec_ref(v___x_429_);
v___x_432_ = lean_st_ref_take(v___y_423_);
v_cache_433_ = lean_ctor_get(v___x_432_, 1);
v_zetaDeltaFVarIds_434_ = lean_ctor_get(v___x_432_, 2);
v_postponed_435_ = lean_ctor_get(v___x_432_, 3);
v_diag_436_ = lean_ctor_get(v___x_432_, 4);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_432_, 0);
lean_dec(v_unused_446_);
v___x_438_ = v___x_432_;
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_diag_436_);
lean_inc(v_postponed_435_);
lean_inc(v_zetaDeltaFVarIds_434_);
lean_inc(v_cache_433_);
lean_dec(v___x_432_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_445_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v_snd_431_);
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_snd_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_cache_433_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_zetaDeltaFVarIds_434_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_postponed_435_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_diag_436_);
v___x_441_ = v_reuseFailAlloc_444_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_st_ref_set(v___y_423_, v___x_441_);
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_fst_430_);
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(lean_object* v_e_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_447_, v___y_448_);
lean_dec(v___y_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(lean_object* v_e_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_451_, v___y_455_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(lean_object* v_e_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(v_e_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(lean_object* v_a_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg___boxed(lean_object* v_a_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(v_a_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(lean_object* v_00_u03b1_487_, lean_object* v_a_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___boxed(lean_object* v_00_u03b1_497_, lean_object* v_a_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(v_00_u03b1_497_, v_a_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(lean_object* v_a_507_, lean_object* v___x_508_, uint8_t v___x_509_, lean_object* v_b_510_, lean_object* v_mk_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
lean_inc(v___x_508_);
v___x_519_ = l_Lean_Elab_Term_elabTerm(v_a_507_, v___x_508_, v___x_509_, v___x_509_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_Elab_Term_elabTerm(v_b_510_, v___x_508_, v___x_509_, v___x_509_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v_a_520_);
v___x_523_ = lean_infer_type(v_a_520_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v_a_522_);
v___x_525_ = lean_infer_type(v_a_522_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Meta_isExprDefEqGuarded(v_a_524_, v_a_526_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_527_) == 0)
{
uint8_t v___x_528_; lean_object* v___x_529_; 
lean_dec_ref_known(v___x_527_, 1);
v___x_528_ = 0;
v___x_529_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_528_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v_a_533_; lean_object* v___x_534_; 
lean_dec_ref_known(v___x_529_, 1);
v___x_530_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_520_, v___y_515_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref(v___x_530_);
v___x_532_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_522_, v___y_515_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref(v___x_532_);
v___x_534_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_531_, v_a_533_, v_mk_511_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_522_);
lean_dec(v_a_520_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
v_a_535_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_529_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_529_);
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
lean_dec(v_a_522_);
lean_dec(v_a_520_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v___x_527_;
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_a_524_);
lean_dec(v_a_522_);
lean_dec(v_a_520_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
v_a_543_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_525_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_525_);
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
lean_dec(v_a_522_);
lean_dec(v_a_520_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
v_a_551_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_523_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_523_);
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
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v_a_520_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
v_a_559_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_521_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_521_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
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
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_574_; 
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v_b_510_);
lean_dec(v___x_508_);
v_a_567_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_574_ == 0)
{
v___x_569_ = v___x_519_;
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_519_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_574_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_567_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed(lean_object* v_a_575_, lean_object* v___x_576_, lean_object* v___x_577_, lean_object* v_b_578_, lean_object* v_mk_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
uint8_t v___x_1677__boxed_587_; lean_object* v_res_588_; 
v___x_1677__boxed_587_ = lean_unbox(v___x_577_);
v_res_588_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(v_a_575_, v___x_576_, v___x_1677__boxed_587_, v_b_578_, v_mk_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v_mk_579_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(lean_object* v_mk_589_, lean_object* v_a_590_, lean_object* v_b_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___f_602_; lean_object* v___x_603_; 
v___x_599_ = lean_box(0);
v___x_600_ = 1;
v___x_601_ = lean_box(v___x_600_);
v___f_602_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed), 12, 5);
lean_closure_set(v___f_602_, 0, v_a_590_);
lean_closure_set(v___f_602_, 1, v___x_599_);
lean_closure_set(v___f_602_, 2, v___x_601_);
lean_closure_set(v___f_602_, 3, v_b_591_);
lean_closure_set(v___f_602_, 4, v_mk_589_);
v___x_603_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_602_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___boxed(lean_object* v_mk_604_, lean_object* v_a_605_, lean_object* v_b_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_mk_604_, v_a_605_, v_b_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
return v_res_614_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_box(0);
v___x_616_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg(){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___boxed(lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(lean_object* v_00_u03b1_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___boxed(lean_object* v_00_u03b1_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(v_00_u03b1_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(lean_object* v_msgData_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; lean_object* v_env_652_; lean_object* v___x_653_; lean_object* v_mctx_654_; lean_object* v_lctx_655_; lean_object* v_options_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_651_ = lean_st_ref_get(v___y_649_);
v_env_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc_ref(v_env_652_);
lean_dec(v___x_651_);
v___x_653_ = lean_st_ref_get(v___y_647_);
v_mctx_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc_ref(v_mctx_654_);
lean_dec(v___x_653_);
v_lctx_655_ = lean_ctor_get(v___y_646_, 2);
v_options_656_ = lean_ctor_get(v___y_648_, 2);
lean_inc_ref(v_options_656_);
lean_inc_ref(v_lctx_655_);
v___x_657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_657_, 0, v_env_652_);
lean_ctor_set(v___x_657_, 1, v_mctx_654_);
lean_ctor_set(v___x_657_, 2, v_lctx_655_);
lean_ctor_set(v___x_657_, 3, v_options_656_);
v___x_658_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v_msgData_645_);
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1___boxed(lean_object* v_msgData_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msgData_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_ref_673_; lean_object* v___x_674_; lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
v_ref_673_ = lean_ctor_get(v___y_670_, 5);
v___x_674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_683_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
lean_inc(v_ref_673_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_ref_673_);
lean_ctor_set(v___x_679_, 1, v_a_675_);
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 1);
lean_ctor_set(v___x_677_, 0, v___x_679_);
v___x_681_ = v___x_677_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg___boxed(lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v_msg_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2));
v___x_696_ = l_Lean_stringToMessageData(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6));
v___x_702_ = l_Lean_stringToMessageData(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(lean_object* v___x_703_, lean_object* v_r_704_, lean_object* v_p_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
if (lean_obj_tag(v___x_703_) == 1)
{
lean_object* v_val_715_; lean_object* v___x_716_; 
v_val_715_ = lean_ctor_get(v___x_703_, 0);
lean_inc_n(v_val_715_, 2);
lean_dec_ref_known(v___x_703_, 1);
lean_inc(v_p_705_);
lean_inc(v_r_704_);
v___x_716_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_val_715_, v_r_704_, v_p_705_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_741_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_741_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_741_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_741_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
uint8_t v___x_721_; 
v___x_721_ = lean_unbox(v_a_717_);
lean_dec(v_a_717_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_del_object(v___x_719_);
v___x_722_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1);
v___x_723_ = l_Lean_MessageData_ofSyntax(v_r_704_);
v___x_724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
v___x_725_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3);
v___x_726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_724_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_715_);
lean_dec(v_val_715_);
v___x_728_ = l_Lean_stringToMessageData(v___x_727_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_MessageData_ofSyntax(v_p_705_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_735_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v_val_715_);
lean_dec(v_p_705_);
lean_dec(v_r_704_);
v___x_737_ = lean_box(0);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_737_);
v___x_739_ = v___x_719_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_val_715_);
lean_dec(v_p_705_);
lean_dec(v_r_704_);
v_a_742_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_716_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_716_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
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
else
{
lean_object* v___x_750_; 
lean_dec(v_p_705_);
lean_dec(v_r_704_);
lean_dec(v___x_703_);
v___x_750_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_750_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(lean_object* v_x_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
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
lean_object* v___x_792_; lean_object* v_eq_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_792_ = lean_unsigned_to_nat(2u);
v_eq_793_ = l_Lean_Syntax_getArg(v_x_777_, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_793_);
v___x_795_ = l_Lean_Syntax_isOfKind(v_eq_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v_eq_793_);
lean_dec(v_x_777_);
v___x_796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v_r_798_; lean_object* v___x_799_; lean_object* v_p_800_; lean_object* v___x_801_; lean_object* v___y_802_; lean_object* v___x_803_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v_r_798_ = l_Lean_Syntax_getArg(v_x_777_, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(3u);
v_p_800_ = l_Lean_Syntax_getArg(v_x_777_, v___x_799_);
lean_dec(v_x_777_);
v___x_801_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_793_);
v___y_802_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 12, 3);
lean_closure_set(v___y_802_, 0, v___x_801_);
lean_closure_set(v___y_802_, 1, v_r_798_);
lean_closure_set(v___y_802_, 2, v_p_800_);
v___x_803_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_802_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_803_;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v_eq_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_804_ = lean_unsigned_to_nat(2u);
v_eq_805_ = l_Lean_Syntax_getArg(v_x_777_, v___x_804_);
v___x_806_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_805_);
v___x_807_ = l_Lean_Syntax_isOfKind(v_eq_805_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; 
lean_dec(v_eq_805_);
lean_dec(v_x_777_);
v___x_808_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_808_;
}
else
{
lean_object* v___x_809_; lean_object* v_r_810_; lean_object* v___x_811_; lean_object* v_p_812_; lean_object* v___x_813_; lean_object* v___y_814_; lean_object* v___x_815_; 
v___x_809_ = lean_unsigned_to_nat(1u);
v_r_810_ = l_Lean_Syntax_getArg(v_x_777_, v___x_809_);
v___x_811_ = lean_unsigned_to_nat(3u);
v_p_812_ = l_Lean_Syntax_getArg(v_x_777_, v___x_811_);
lean_dec(v_x_777_);
v___x_813_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_805_);
v___y_814_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed), 12, 3);
lean_closure_set(v___y_814_, 0, v___x_813_);
lean_closure_set(v___y_814_, 1, v_r_810_);
lean_closure_set(v___y_814_, 2, v_p_812_);
v___x_815_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_814_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed(lean_object* v_x_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(v_x_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(lean_object* v_00_u03b1_827_, lean_object* v_msg_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v_msg_828_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___boxed(lean_object* v_00_u03b1_839_, lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(v_00_u03b1_839_, v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1(){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_861_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_862_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2));
v___x_863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3));
v___x_864_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed), 10, 0);
v___x_865_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_861_, v___x_862_, v___x_863_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___boxed(lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3(){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3));
v___x_895_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6));
v___x_896_ = l_Lean_addBuiltinDeclarationRanges(v___x_894_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___boxed(lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1(){
_start:
{
lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___f_929_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed), 10, 0);
v___x_930_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4));
v___x_932_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1));
v___x_933_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_930_, v___x_931_, v___x_932_, v___f_929_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___boxed(lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3(){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1));
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6));
v___x_964_ = l_Lean_addBuiltinDeclarationRanges(v___x_962_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___boxed(lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(lean_object* v_e_967_, lean_object* v___y_968_){
_start:
{
uint8_t v___x_970_; 
v___x_970_ = l_Lean_Expr_hasMVar(v_e_967_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_e_967_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; lean_object* v_mctx_973_; lean_object* v___x_974_; lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___x_977_; lean_object* v_cache_978_; lean_object* v_zetaDeltaFVarIds_979_; lean_object* v_postponed_980_; lean_object* v_diag_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_990_; 
v___x_972_ = lean_st_ref_get(v___y_968_);
v_mctx_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc_ref(v_mctx_973_);
lean_dec(v___x_972_);
v___x_974_ = l_Lean_instantiateMVarsCore(v_mctx_973_, v_e_967_);
v_fst_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_fst_975_);
v_snd_976_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_snd_976_);
lean_dec_ref(v___x_974_);
v___x_977_ = lean_st_ref_take(v___y_968_);
v_cache_978_ = lean_ctor_get(v___x_977_, 1);
v_zetaDeltaFVarIds_979_ = lean_ctor_get(v___x_977_, 2);
v_postponed_980_ = lean_ctor_get(v___x_977_, 3);
v_diag_981_ = lean_ctor_get(v___x_977_, 4);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_991_);
v___x_983_ = v___x_977_;
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_diag_981_);
lean_inc(v_postponed_980_);
lean_inc(v_zetaDeltaFVarIds_979_);
lean_inc(v_cache_978_);
lean_dec(v___x_977_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v_snd_976_);
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_snd_976_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_cache_978_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_zetaDeltaFVarIds_979_);
lean_ctor_set(v_reuseFailAlloc_989_, 3, v_postponed_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 4, v_diag_981_);
v___x_986_ = v_reuseFailAlloc_989_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = lean_st_ref_set(v___y_968_, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_fst_975_);
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg___boxed(lean_object* v_e_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_992_, v___y_993_);
lean_dec(v___y_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(lean_object* v_e_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_996_, v___y_1002_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___boxed(lean_object* v_e_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(v_e_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(lean_object* v_getTgt_1024_, lean_object* v_r_1025_, lean_object* v_eq_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v___x_1036_; 
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
v___x_1036_ = lean_apply_9(v_getTgt_1024_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, lean_box(0));
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1038_; lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1097_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v___x_1038_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_a_1037_, v___y_1032_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1097_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1097_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; 
lean_inc(v___y_1034_);
lean_inc_ref(v___y_1033_);
lean_inc(v___y_1032_);
lean_inc_ref(v___y_1031_);
lean_inc(v_a_1039_);
v___x_1043_ = lean_infer_type(v_a_1039_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1046_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 1);
lean_ctor_set(v___x_1041_, 0, v_a_1044_);
v___x_1046_ = v___x_1041_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1044_);
v___x_1046_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
uint8_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = 0;
v___x_1048_ = l_Lean_Elab_Tactic_elabTerm(v_r_1025_, v___x_1046_, v___x_1047_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v___x_1050_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_1026_);
if (lean_obj_tag(v___x_1050_) == 1)
{
lean_object* v_val_1051_; lean_object* v___x_1052_; 
v_val_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v___x_1050_, 1);
lean_inc(v_a_1039_);
lean_inc(v_a_1049_);
v___x_1052_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1049_, v_a_1039_, v_val_1051_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v_val_1051_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1070_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1070_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1070_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_unbox(v_a_1053_);
lean_dec(v_a_1053_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_del_object(v___x_1055_);
v___x_1058_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1);
v___x_1059_ = l_Lean_indentExpr(v_a_1039_);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = l_Lean_indentExpr(v_a_1049_);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1064_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_dec(v_a_1049_);
lean_dec(v_a_1039_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
v___x_1066_ = lean_box(0);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1066_);
v___x_1068_ = v___x_1055_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_a_1049_);
lean_dec(v_a_1039_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
v_a_1071_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1052_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1052_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
else
{
lean_object* v___x_1079_; 
lean_dec(v___x_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1039_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
v___x_1079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1079_;
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_a_1039_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v_eq_1026_);
v_a_1080_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1048_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1048_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
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
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_del_object(v___x_1041_);
lean_dec(v_a_1039_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v_eq_1026_);
lean_dec(v_r_1025_);
v_a_1089_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1043_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1043_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v_eq_1026_);
lean_dec(v_r_1025_);
v_a_1098_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1036_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1036_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed(lean_object* v_getTgt_1106_, lean_object* v_r_1107_, lean_object* v_eq_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(v_getTgt_1106_, v_r_1107_, v_eq_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(lean_object* v_x_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_eq_1144_; lean_object* v_r_1145_; lean_object* v_getTgt_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1));
lean_inc(v_x_1133_);
v___x_1158_ = l_Lean_Syntax_isOfKind(v_x_1133_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3));
lean_inc(v_x_1133_);
v___x_1160_ = l_Lean_Syntax_isOfKind(v_x_1133_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
lean_dec(v_x_1133_);
v___x_1161_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; lean_object* v_eq_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v_eq_1163_ = l_Lean_Syntax_getArg(v_x_1133_, v___x_1162_);
v___x_1164_ = lean_unsigned_to_nat(2u);
v___x_1165_ = l_Lean_Syntax_getArg(v_x_1133_, v___x_1164_);
lean_dec(v_x_1133_);
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4));
v_eq_1144_ = v_eq_1163_;
v_r_1145_ = v___x_1165_;
v_getTgt_1146_ = v___x_1166_;
v___y_1147_ = v_a_1134_;
v___y_1148_ = v_a_1135_;
v___y_1149_ = v_a_1136_;
v___y_1150_ = v_a_1137_;
v___y_1151_ = v_a_1138_;
v___y_1152_ = v_a_1139_;
v___y_1153_ = v_a_1140_;
v___y_1154_ = v_a_1141_;
goto v___jp_1143_;
}
}
else
{
lean_object* v___x_1167_; lean_object* v_eq_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1167_ = lean_unsigned_to_nat(1u);
v_eq_1168_ = l_Lean_Syntax_getArg(v_x_1133_, v___x_1167_);
v___x_1169_ = lean_unsigned_to_nat(2u);
v___x_1170_ = l_Lean_Syntax_getArg(v_x_1133_, v___x_1169_);
lean_dec(v_x_1133_);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5));
v_eq_1144_ = v_eq_1168_;
v_r_1145_ = v___x_1170_;
v_getTgt_1146_ = v___x_1171_;
v___y_1147_ = v_a_1134_;
v___y_1148_ = v_a_1135_;
v___y_1149_ = v_a_1136_;
v___y_1150_ = v_a_1137_;
v___y_1151_ = v_a_1138_;
v___y_1152_ = v_a_1139_;
v___y_1153_ = v_a_1140_;
v___y_1154_ = v_a_1141_;
goto v___jp_1143_;
}
v___jp_1143_:
{
lean_object* v___f_1155_; lean_object* v___x_1156_; 
lean_inc_ref(v_getTgt_1146_);
v___f_1155_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed), 12, 3);
lean_closure_set(v___f_1155_, 0, v_getTgt_1146_);
lean_closure_set(v___f_1155_, 1, v_r_1145_);
lean_closure_set(v___f_1155_, 2, v_eq_1144_);
v___x_1156_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1155_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed(lean_object* v_x_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(v_x_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1(){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1191_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1192_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1));
v___x_1193_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1));
v___x_1194_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed), 10, 0);
v___x_1195_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1191_, v___x_1192_, v___x_1193_, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___boxed(lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3(){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1));
v___x_1225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6));
v___x_1226_ = l_Lean_addBuiltinDeclarationRanges(v___x_1224_, v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___boxed(lean_object* v_a_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1(){
_start:
{
lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed), 10, 0);
v___x_1260_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1261_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3));
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1));
v___x_1263_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1260_, v___x_1261_, v___x_1262_, v___f_1259_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___boxed(lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3(){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1));
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6));
v___x_1294_ = l_Lean_addBuiltinDeclarationRanges(v___x_1292_, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___boxed(lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6));
v___x_1308_ = l_Lean_stringToMessageData(v___x_1307_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8));
v___x_1311_ = l_Lean_stringToMessageData(v___x_1310_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10));
v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14));
v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(lean_object* v___x_1321_, uint8_t v___x_1322_, lean_object* v_val_1323_, lean_object* v_eq_1324_, lean_object* v_c_1325_, lean_object* v_ty_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v_lDecl_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___x_1471_; 
lean_inc(v___x_1321_);
v___x_1471_ = l_Lean_Elab_Tactic_getFVarId(v___x_1321_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v_lctx_1473_; lean_object* v___x_1474_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v_lctx_1473_ = lean_ctor_get(v___y_1331_, 2);
lean_inc_ref(v_lctx_1473_);
v___x_1474_ = lean_local_ctx_find(v_lctx_1473_, v_a_1472_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_ty_1326_);
lean_dec(v_c_1325_);
lean_dec(v_eq_1324_);
lean_dec(v_val_1323_);
v___x_1475_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1476_ = l_Lean_MessageData_ofSyntax(v___x_1321_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1479_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec_ref(v___y_1331_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_val_1489_; 
v_val_1489_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v___x_1474_, 1);
v_lDecl_1420_ = v_val_1489_;
v___y_1421_ = v___y_1327_;
v___y_1422_ = v___y_1328_;
v___y_1423_ = v___y_1329_;
v___y_1424_ = v___y_1330_;
v___y_1425_ = v___y_1331_;
v___y_1426_ = v___y_1332_;
v___y_1427_ = v___y_1333_;
v___y_1428_ = v___y_1334_;
goto v___jp_1419_;
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v___y_1331_);
lean_dec(v_ty_1326_);
lean_dec(v_c_1325_);
lean_dec(v_eq_1324_);
lean_dec(v_val_1323_);
lean_dec(v___x_1321_);
v_a_1490_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1471_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1471_);
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
v___jp_1336_:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_LocalDecl_value_x3f(v___y_1337_, v___x_1322_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_dec_ref(v___y_1337_);
lean_dec(v_eq_1324_);
if (lean_obj_tag(v_val_1323_) == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v___y_1342_);
lean_dec(v___x_1321_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_dec_ref_known(v_val_1323_, 1);
v___x_1349_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1350_ = l_Lean_MessageData_ofSyntax(v___x_1321_);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1353_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___y_1342_);
return v___x_1354_;
}
}
else
{
if (lean_obj_tag(v_val_1323_) == 0)
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec_ref_known(v___x_1346_, 1);
lean_dec_ref(v___y_1337_);
lean_dec(v_eq_1324_);
v___x_1355_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1356_ = l_Lean_MessageData_ofSyntax(v___x_1321_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3);
v___x_1359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1359_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___y_1342_);
return v___x_1360_;
}
else
{
if (lean_obj_tag(v_eq_1324_) == 0)
{
lean_object* v___x_1361_; 
lean_dec_ref_known(v_val_1323_, 1);
lean_dec_ref_known(v___x_1346_, 1);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v___y_1337_);
lean_dec(v___x_1321_);
v___x_1361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1361_;
}
else
{
lean_object* v_val_1362_; lean_object* v_val_1363_; lean_object* v_val_1364_; lean_object* v___x_1365_; 
v_val_1362_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1346_, 1);
v_val_1363_ = lean_ctor_get(v_val_1323_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v_val_1323_, 1);
v_val_1364_ = lean_ctor_get(v_eq_1324_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v_eq_1324_, 1);
v___x_1365_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_1364_);
if (lean_obj_tag(v___x_1365_) == 1)
{
lean_object* v_val_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1417_; 
v_val_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1417_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_val_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1417_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = l_Lean_LocalDecl_type(v___y_1337_);
lean_dec_ref(v___y_1337_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Elab_Tactic_elabTerm(v_val_1363_, v___x_1372_, v___x_1322_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; lean_object* v_a_1376_; lean_object* v___x_1377_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc_n(v_a_1374_, 2);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_1362_, v___y_1343_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_n(v_a_1376_, 2);
lean_dec_ref(v___x_1375_);
v___x_1377_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1374_, v_a_1376_, v_val_1366_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v_val_1366_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1399_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1399_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1399_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_unbox(v_a_1378_);
lean_dec(v_a_1378_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_del_object(v___x_1380_);
v___x_1383_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1384_ = l_Lean_MessageData_ofSyntax(v___x_1321_);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_indentExpr(v_a_1376_);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9);
v___x_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = l_Lean_indentExpr(v_a_1374_);
v___x_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
v___x_1394_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1393_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___y_1342_);
return v___x_1394_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1397_; 
lean_dec(v_a_1376_);
lean_dec(v_a_1374_);
lean_dec_ref(v___y_1342_);
lean_dec(v___x_1321_);
v___x_1395_ = lean_box(0);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1395_);
v___x_1397_ = v___x_1380_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec(v_a_1376_);
lean_dec(v_a_1374_);
lean_dec_ref(v___y_1342_);
lean_dec(v___x_1321_);
v_a_1400_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1377_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1377_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_val_1366_);
lean_dec(v_val_1362_);
lean_dec_ref(v___y_1342_);
lean_dec(v___x_1321_);
v_a_1408_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1373_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1373_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
else
{
lean_object* v___x_1418_; 
lean_dec(v___x_1365_);
lean_dec(v_val_1363_);
lean_dec(v_val_1362_);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v___y_1337_);
lean_dec(v___x_1321_);
v___x_1418_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1418_;
}
}
}
}
}
v___jp_1419_:
{
if (lean_obj_tag(v_c_1325_) == 1)
{
if (lean_obj_tag(v_ty_1326_) == 1)
{
lean_object* v_val_1429_; lean_object* v_val_1430_; lean_object* v___x_1431_; 
v_val_1429_ = lean_ctor_get(v_c_1325_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v_c_1325_, 1);
v_val_1430_ = lean_ctor_get(v_ty_1326_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v_ty_1326_, 1);
v___x_1431_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_1429_);
if (lean_obj_tag(v___x_1431_) == 1)
{
lean_object* v_val_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_val_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_box(0);
v___x_1434_ = l_Lean_Elab_Tactic_elabTerm(v_val_1430_, v___x_1433_, v___x_1322_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_n(v_a_1435_, 2);
lean_dec_ref_known(v___x_1434_, 1);
v___x_1436_ = l_Lean_LocalDecl_type(v_lDecl_1420_);
v___x_1437_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_1436_, v___y_1426_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_n(v_a_1438_, 2);
lean_dec_ref(v___x_1437_);
v___x_1439_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1435_, v_a_1438_, v_val_1432_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec(v_val_1432_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; uint8_t v___x_1441_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = lean_unbox(v_a_1440_);
lean_dec(v_a_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
lean_dec_ref(v_lDecl_1420_);
lean_dec(v_eq_1324_);
lean_dec(v_val_1323_);
v___x_1442_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1443_ = l_Lean_MessageData_ofSyntax(v___x_1321_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Lean_indentExpr(v_a_1438_);
v___x_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = l_Lean_indentExpr(v_a_1435_);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1452_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
lean_dec_ref(v___y_1425_);
return v___x_1453_;
}
else
{
lean_dec(v_a_1438_);
lean_dec(v_a_1435_);
v___y_1337_ = v_lDecl_1420_;
v___y_1338_ = v___y_1421_;
v___y_1339_ = v___y_1422_;
v___y_1340_ = v___y_1423_;
v___y_1341_ = v___y_1424_;
v___y_1342_ = v___y_1425_;
v___y_1343_ = v___y_1426_;
v___y_1344_ = v___y_1427_;
v___y_1345_ = v___y_1428_;
goto v___jp_1336_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_a_1438_);
lean_dec(v_a_1435_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v_lDecl_1420_);
lean_dec(v_eq_1324_);
lean_dec(v_val_1323_);
lean_dec(v___x_1321_);
v_a_1454_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1439_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1439_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_val_1432_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v_lDecl_1420_);
lean_dec(v_eq_1324_);
lean_dec(v_val_1323_);
lean_dec(v___x_1321_);
v_a_1462_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1434_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1434_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v___x_1470_; 
lean_dec(v___x_1431_);
lean_dec(v_val_1430_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v_lDecl_1420_);
lean_dec(v_eq_1324_);
lean_dec(v_val_1323_);
lean_dec(v___x_1321_);
v___x_1470_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1470_;
}
}
else
{
lean_dec_ref_known(v_c_1325_, 1);
lean_dec(v_ty_1326_);
v___y_1337_ = v_lDecl_1420_;
v___y_1338_ = v___y_1421_;
v___y_1339_ = v___y_1422_;
v___y_1340_ = v___y_1423_;
v___y_1341_ = v___y_1424_;
v___y_1342_ = v___y_1425_;
v___y_1343_ = v___y_1426_;
v___y_1344_ = v___y_1427_;
v___y_1345_ = v___y_1428_;
goto v___jp_1336_;
}
}
else
{
lean_dec(v_ty_1326_);
lean_dec(v_c_1325_);
v___y_1337_ = v_lDecl_1420_;
v___y_1338_ = v___y_1421_;
v___y_1339_ = v___y_1422_;
v___y_1340_ = v___y_1423_;
v___y_1341_ = v___y_1424_;
v___y_1342_ = v___y_1425_;
v___y_1343_ = v___y_1426_;
v___y_1344_ = v___y_1427_;
v___y_1345_ = v___y_1428_;
goto v___jp_1336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed(lean_object* v___x_1498_, lean_object* v___x_1499_, lean_object* v_val_1500_, lean_object* v_eq_1501_, lean_object* v_c_1502_, lean_object* v_ty_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
uint8_t v___x_14521__boxed_1513_; lean_object* v_res_1514_; 
v___x_14521__boxed_1513_ = lean_unbox(v___x_1499_);
v_res_1514_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(v___x_1498_, v___x_14521__boxed_1513_, v_val_1500_, v_eq_1501_, v_c_1502_, v_ty_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(lean_object* v___x_1515_, lean_object* v_val_1516_, lean_object* v_eq_1517_, lean_object* v_c_1518_, lean_object* v_ty_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_lDecl_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___y_1622_; lean_object* v___x_1666_; 
lean_inc(v___x_1515_);
v___x_1666_ = l_Lean_Elab_Tactic_getFVarId(v___x_1515_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v_lctx_1668_; lean_object* v___x_1669_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v_lctx_1668_ = lean_ctor_get(v___y_1524_, 2);
lean_inc_ref(v_lctx_1668_);
v___x_1669_ = lean_local_ctx_find(v_lctx_1668_, v_a_1667_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_ty_1519_);
lean_dec(v_c_1518_);
lean_dec(v_eq_1517_);
lean_dec(v_val_1516_);
v___x_1670_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1671_ = l_Lean_MessageData_ofSyntax(v___x_1515_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1674_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec_ref(v___y_1524_);
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
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
else
{
lean_object* v_val_1684_; 
v_val_1684_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1669_, 1);
v_lDecl_1614_ = v_val_1684_;
v___y_1615_ = v___y_1520_;
v___y_1616_ = v___y_1521_;
v___y_1617_ = v___y_1522_;
v___y_1618_ = v___y_1523_;
v___y_1619_ = v___y_1524_;
v___y_1620_ = v___y_1525_;
v___y_1621_ = v___y_1526_;
v___y_1622_ = v___y_1527_;
goto v___jp_1613_;
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v___y_1524_);
lean_dec(v_ty_1519_);
lean_dec(v_c_1518_);
lean_dec(v_eq_1517_);
lean_dec(v_val_1516_);
lean_dec(v___x_1515_);
v_a_1685_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1666_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1666_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
v___jp_1529_:
{
uint8_t v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = 0;
v___x_1540_ = l_Lean_LocalDecl_value_x3f(v___y_1530_, v___x_1539_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_dec_ref(v___y_1530_);
lean_dec(v_eq_1517_);
if (lean_obj_tag(v_val_1516_) == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec_ref(v___y_1535_);
lean_dec(v___x_1515_);
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
else
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec_ref_known(v_val_1516_, 1);
v___x_1543_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1544_ = l_Lean_MessageData_ofSyntax(v___x_1515_);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1547_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___y_1535_);
return v___x_1548_;
}
}
else
{
if (lean_obj_tag(v_val_1516_) == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
lean_dec_ref_known(v___x_1540_, 1);
lean_dec_ref(v___y_1530_);
lean_dec(v_eq_1517_);
v___x_1549_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_1550_ = l_Lean_MessageData_ofSyntax(v___x_1515_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1553_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___y_1535_);
return v___x_1554_;
}
else
{
if (lean_obj_tag(v_eq_1517_) == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref_known(v_val_1516_, 1);
lean_dec_ref_known(v___x_1540_, 1);
lean_dec_ref(v___y_1535_);
lean_dec_ref(v___y_1530_);
lean_dec(v___x_1515_);
v___x_1555_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1555_;
}
else
{
lean_object* v_val_1556_; lean_object* v_val_1557_; lean_object* v_val_1558_; lean_object* v___x_1559_; 
v_val_1556_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v___x_1540_, 1);
v_val_1557_ = lean_ctor_get(v_val_1516_, 0);
lean_inc(v_val_1557_);
lean_dec_ref_known(v_val_1516_, 1);
v_val_1558_ = lean_ctor_get(v_eq_1517_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v_eq_1517_, 1);
v___x_1559_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_1558_);
if (lean_obj_tag(v___x_1559_) == 1)
{
lean_object* v_val_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1611_; 
v_val_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1611_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_val_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1611_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = l_Lean_LocalDecl_type(v___y_1530_);
lean_dec_ref(v___y_1530_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Elab_Tactic_elabTerm(v_val_1557_, v___x_1566_, v___x_1539_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc_n(v_a_1568_, 2);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_1556_, v___y_1536_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_n(v_a_1570_, 2);
lean_dec_ref(v___x_1569_);
v___x_1571_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1568_, v_a_1570_, v_val_1560_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec(v_val_1560_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1593_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1593_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1593_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
uint8_t v___x_1576_; 
v___x_1576_ = lean_unbox(v_a_1572_);
lean_dec(v_a_1572_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
lean_del_object(v___x_1574_);
v___x_1577_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1578_ = l_Lean_MessageData_ofSyntax(v___x_1515_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_indentExpr(v_a_1570_);
v___x_1583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1581_);
lean_ctor_set(v___x_1583_, 1, v___x_1582_);
v___x_1584_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = l_Lean_indentExpr(v_a_1568_);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
v___x_1588_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1587_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
lean_dec_ref(v___y_1535_);
return v___x_1588_;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_dec(v_a_1570_);
lean_dec(v_a_1568_);
lean_dec_ref(v___y_1535_);
lean_dec(v___x_1515_);
v___x_1589_ = lean_box(0);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1589_);
v___x_1591_ = v___x_1574_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1570_);
lean_dec(v_a_1568_);
lean_dec_ref(v___y_1535_);
lean_dec(v___x_1515_);
v_a_1594_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1571_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1571_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_val_1560_);
lean_dec(v_val_1556_);
lean_dec_ref(v___y_1535_);
lean_dec(v___x_1515_);
v_a_1602_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1567_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1567_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
else
{
lean_object* v___x_1612_; 
lean_dec(v___x_1559_);
lean_dec(v_val_1557_);
lean_dec(v_val_1556_);
lean_dec_ref(v___y_1535_);
lean_dec_ref(v___y_1530_);
lean_dec(v___x_1515_);
v___x_1612_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1612_;
}
}
}
}
}
v___jp_1613_:
{
if (lean_obj_tag(v_c_1518_) == 1)
{
if (lean_obj_tag(v_ty_1519_) == 1)
{
lean_object* v_val_1623_; lean_object* v_val_1624_; lean_object* v___x_1625_; 
v_val_1623_ = lean_ctor_get(v_c_1518_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_c_1518_, 1);
v_val_1624_ = lean_ctor_get(v_ty_1519_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v_ty_1519_, 1);
v___x_1625_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_1623_);
if (lean_obj_tag(v___x_1625_) == 1)
{
lean_object* v_val_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v_val_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1627_ = lean_box(0);
v___x_1628_ = 0;
v___x_1629_ = l_Lean_Elab_Tactic_elabTerm(v_val_1624_, v___x_1627_, v___x_1628_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc_n(v_a_1630_, 2);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = l_Lean_LocalDecl_type(v_lDecl_1614_);
v___x_1632_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_1631_, v___y_1620_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_n(v_a_1633_, 2);
lean_dec_ref(v___x_1632_);
v___x_1634_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(v_a_1630_, v_a_1633_, v_val_1626_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v_val_1626_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; uint8_t v___x_1636_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1636_ = lean_unbox(v_a_1635_);
lean_dec(v_a_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v_lDecl_1614_);
lean_dec(v_eq_1517_);
lean_dec(v_val_1516_);
v___x_1637_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
v___x_1638_ = l_Lean_MessageData_ofSyntax(v___x_1515_);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_indentExpr(v_a_1633_);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13, &l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_indentExpr(v_a_1630_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_1647_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec_ref(v___y_1619_);
return v___x_1648_;
}
else
{
lean_dec(v_a_1633_);
lean_dec(v_a_1630_);
v___y_1530_ = v_lDecl_1614_;
v___y_1531_ = v___y_1615_;
v___y_1532_ = v___y_1616_;
v___y_1533_ = v___y_1617_;
v___y_1534_ = v___y_1618_;
v___y_1535_ = v___y_1619_;
v___y_1536_ = v___y_1620_;
v___y_1537_ = v___y_1621_;
v___y_1538_ = v___y_1622_;
goto v___jp_1529_;
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1633_);
lean_dec(v_a_1630_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_lDecl_1614_);
lean_dec(v_eq_1517_);
lean_dec(v_val_1516_);
lean_dec(v___x_1515_);
v_a_1649_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1634_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1634_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec(v_val_1626_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_lDecl_1614_);
lean_dec(v_eq_1517_);
lean_dec(v_val_1516_);
lean_dec(v___x_1515_);
v_a_1657_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1629_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1629_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v___x_1665_; 
lean_dec(v___x_1625_);
lean_dec(v_val_1624_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_lDecl_1614_);
lean_dec(v_eq_1517_);
lean_dec(v_val_1516_);
lean_dec(v___x_1515_);
v___x_1665_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1665_;
}
}
else
{
lean_dec_ref_known(v_c_1518_, 1);
lean_dec(v_ty_1519_);
v___y_1530_ = v_lDecl_1614_;
v___y_1531_ = v___y_1615_;
v___y_1532_ = v___y_1616_;
v___y_1533_ = v___y_1617_;
v___y_1534_ = v___y_1618_;
v___y_1535_ = v___y_1619_;
v___y_1536_ = v___y_1620_;
v___y_1537_ = v___y_1621_;
v___y_1538_ = v___y_1622_;
goto v___jp_1529_;
}
}
else
{
lean_dec(v_ty_1519_);
lean_dec(v_c_1518_);
v___y_1530_ = v_lDecl_1614_;
v___y_1531_ = v___y_1615_;
v___y_1532_ = v___y_1616_;
v___y_1533_ = v___y_1617_;
v___y_1534_ = v___y_1618_;
v___y_1535_ = v___y_1619_;
v___y_1536_ = v___y_1620_;
v___y_1537_ = v___y_1621_;
v___y_1538_ = v___y_1622_;
goto v___jp_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed(lean_object* v___x_1693_, lean_object* v_val_1694_, lean_object* v_eq_1695_, lean_object* v_c_1696_, lean_object* v_ty_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(v___x_1693_, v_val_1694_, v_eq_1695_, v_c_1696_, v_ty_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(lean_object* v_x_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1));
lean_inc(v_x_1720_);
v___x_1731_ = l_Lean_Syntax_isOfKind(v_x_1720_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3));
lean_inc(v_x_1720_);
v___x_1733_ = l_Lean_Syntax_isOfKind(v_x_1720_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec(v_x_1720_);
v___x_1734_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1734_;
}
else
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v_eq_1749_; lean_object* v_val_1750_; lean_object* v___x_1754_; lean_object* v_c_1756_; lean_object* v_ty_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1735_ = lean_unsigned_to_nat(0u);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = l_Lean_Syntax_getArg(v_x_1720_, v___x_1736_);
v___x_1754_ = lean_unsigned_to_nat(2u);
v___x_1776_ = l_Lean_Syntax_getArg(v_x_1720_, v___x_1754_);
v___x_1777_ = l_Lean_Syntax_isNone(v___x_1776_);
if (v___x_1777_ == 0)
{
uint8_t v___x_1778_; 
lean_inc(v___x_1776_);
v___x_1778_ = l_Lean_Syntax_matchesNull(v___x_1776_, v___x_1754_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; 
lean_dec(v___x_1776_);
lean_dec(v___x_1737_);
lean_dec(v_x_1720_);
v___x_1779_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1779_;
}
else
{
lean_object* v_c_1780_; lean_object* v_ty_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_c_1780_ = l_Lean_Syntax_getArg(v___x_1776_, v___x_1735_);
v_ty_1781_ = l_Lean_Syntax_getArg(v___x_1776_, v___x_1736_);
lean_dec(v___x_1776_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_c_1780_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_ty_1781_);
v_c_1756_ = v___x_1782_;
v_ty_1757_ = v___x_1783_;
v___y_1758_ = v_a_1721_;
v___y_1759_ = v_a_1722_;
v___y_1760_ = v_a_1723_;
v___y_1761_ = v_a_1724_;
v___y_1762_ = v_a_1725_;
v___y_1763_ = v_a_1726_;
v___y_1764_ = v_a_1727_;
v___y_1765_ = v_a_1728_;
goto v___jp_1755_;
}
}
else
{
lean_object* v___x_1784_; 
lean_dec(v___x_1776_);
v___x_1784_ = lean_box(0);
v_c_1756_ = v___x_1784_;
v_ty_1757_ = v___x_1784_;
v___y_1758_ = v_a_1721_;
v___y_1759_ = v_a_1722_;
v___y_1760_ = v_a_1723_;
v___y_1761_ = v_a_1724_;
v___y_1762_ = v_a_1725_;
v___y_1763_ = v_a_1726_;
v___y_1764_ = v_a_1727_;
v___y_1765_ = v_a_1728_;
goto v___jp_1755_;
}
v___jp_1738_:
{
lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_box(v___x_1731_);
v___f_1752_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed), 15, 6);
lean_closure_set(v___f_1752_, 0, v___x_1737_);
lean_closure_set(v___f_1752_, 1, v___x_1751_);
lean_closure_set(v___f_1752_, 2, v_val_1750_);
lean_closure_set(v___f_1752_, 3, v_eq_1749_);
lean_closure_set(v___f_1752_, 4, v___y_1746_);
lean_closure_set(v___f_1752_, 5, v___y_1745_);
v___x_1753_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1752_, v___y_1748_, v___y_1744_, v___y_1741_, v___y_1740_, v___y_1747_, v___y_1742_, v___y_1743_, v___y_1739_);
return v___x_1753_;
}
v___jp_1755_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = lean_unsigned_to_nat(3u);
v___x_1767_ = l_Lean_Syntax_getArg(v_x_1720_, v___x_1766_);
lean_dec(v_x_1720_);
v___x_1768_ = l_Lean_Syntax_isNone(v___x_1767_);
if (v___x_1768_ == 0)
{
uint8_t v___x_1769_; 
lean_inc(v___x_1767_);
v___x_1769_ = l_Lean_Syntax_matchesNull(v___x_1767_, v___x_1754_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
lean_dec(v___x_1767_);
lean_dec(v_ty_1757_);
lean_dec(v_c_1756_);
lean_dec(v___x_1737_);
v___x_1770_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1770_;
}
else
{
lean_object* v_eq_1771_; lean_object* v_val_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_eq_1771_ = l_Lean_Syntax_getArg(v___x_1767_, v___x_1735_);
v_val_1772_ = l_Lean_Syntax_getArg(v___x_1767_, v___x_1736_);
lean_dec(v___x_1767_);
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_eq_1771_);
v___x_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_val_1772_);
v___y_1739_ = v___y_1765_;
v___y_1740_ = v___y_1761_;
v___y_1741_ = v___y_1760_;
v___y_1742_ = v___y_1763_;
v___y_1743_ = v___y_1764_;
v___y_1744_ = v___y_1759_;
v___y_1745_ = v_ty_1757_;
v___y_1746_ = v_c_1756_;
v___y_1747_ = v___y_1762_;
v___y_1748_ = v___y_1758_;
v_eq_1749_ = v___x_1773_;
v_val_1750_ = v___x_1774_;
goto v___jp_1738_;
}
}
else
{
lean_object* v___x_1775_; 
lean_dec(v___x_1767_);
v___x_1775_ = lean_box(0);
v___y_1739_ = v___y_1765_;
v___y_1740_ = v___y_1761_;
v___y_1741_ = v___y_1760_;
v___y_1742_ = v___y_1763_;
v___y_1743_ = v___y_1764_;
v___y_1744_ = v___y_1759_;
v___y_1745_ = v_ty_1757_;
v___y_1746_ = v_c_1756_;
v___y_1747_ = v___y_1762_;
v___y_1748_ = v___y_1758_;
v_eq_1749_ = v___x_1775_;
v_val_1750_ = v___x_1775_;
goto v___jp_1738_;
}
}
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v_eq_1799_; lean_object* v_val_1800_; lean_object* v___x_1803_; lean_object* v_c_1805_; lean_object* v_ty_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1785_ = lean_unsigned_to_nat(0u);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = l_Lean_Syntax_getArg(v_x_1720_, v___x_1786_);
v___x_1803_ = lean_unsigned_to_nat(2u);
v___x_1825_ = l_Lean_Syntax_getArg(v_x_1720_, v___x_1803_);
v___x_1826_ = l_Lean_Syntax_isNone(v___x_1825_);
if (v___x_1826_ == 0)
{
uint8_t v___x_1827_; 
lean_inc(v___x_1825_);
v___x_1827_ = l_Lean_Syntax_matchesNull(v___x_1825_, v___x_1803_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec(v___x_1825_);
lean_dec(v___x_1787_);
lean_dec(v_x_1720_);
v___x_1828_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1828_;
}
else
{
lean_object* v_c_1829_; lean_object* v_ty_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_c_1829_ = l_Lean_Syntax_getArg(v___x_1825_, v___x_1785_);
v_ty_1830_ = l_Lean_Syntax_getArg(v___x_1825_, v___x_1786_);
lean_dec(v___x_1825_);
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_c_1829_);
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_ty_1830_);
v_c_1805_ = v___x_1831_;
v_ty_1806_ = v___x_1832_;
v___y_1807_ = v_a_1721_;
v___y_1808_ = v_a_1722_;
v___y_1809_ = v_a_1723_;
v___y_1810_ = v_a_1724_;
v___y_1811_ = v_a_1725_;
v___y_1812_ = v_a_1726_;
v___y_1813_ = v_a_1727_;
v___y_1814_ = v_a_1728_;
goto v___jp_1804_;
}
}
else
{
lean_object* v___x_1833_; 
lean_dec(v___x_1825_);
v___x_1833_ = lean_box(0);
v_c_1805_ = v___x_1833_;
v_ty_1806_ = v___x_1833_;
v___y_1807_ = v_a_1721_;
v___y_1808_ = v_a_1722_;
v___y_1809_ = v_a_1723_;
v___y_1810_ = v_a_1724_;
v___y_1811_ = v_a_1725_;
v___y_1812_ = v_a_1726_;
v___y_1813_ = v_a_1727_;
v___y_1814_ = v_a_1728_;
goto v___jp_1804_;
}
v___jp_1788_:
{
lean_object* v___f_1801_; lean_object* v___x_1802_; 
v___f_1801_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed), 14, 5);
lean_closure_set(v___f_1801_, 0, v___x_1787_);
lean_closure_set(v___f_1801_, 1, v_val_1800_);
lean_closure_set(v___f_1801_, 2, v_eq_1799_);
lean_closure_set(v___f_1801_, 3, v___y_1795_);
lean_closure_set(v___f_1801_, 4, v___y_1790_);
v___x_1802_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1801_, v___y_1796_, v___y_1791_, v___y_1797_, v___y_1798_, v___y_1793_, v___y_1789_, v___y_1794_, v___y_1792_);
return v___x_1802_;
}
v___jp_1804_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1815_ = lean_unsigned_to_nat(3u);
v___x_1816_ = l_Lean_Syntax_getArg(v_x_1720_, v___x_1815_);
lean_dec(v_x_1720_);
v___x_1817_ = l_Lean_Syntax_isNone(v___x_1816_);
if (v___x_1817_ == 0)
{
uint8_t v___x_1818_; 
lean_inc(v___x_1816_);
v___x_1818_ = l_Lean_Syntax_matchesNull(v___x_1816_, v___x_1803_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
lean_dec(v___x_1816_);
lean_dec(v_ty_1806_);
lean_dec(v_c_1805_);
lean_dec(v___x_1787_);
v___x_1819_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
return v___x_1819_;
}
else
{
lean_object* v_eq_1820_; lean_object* v_val_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_eq_1820_ = l_Lean_Syntax_getArg(v___x_1816_, v___x_1785_);
v_val_1821_ = l_Lean_Syntax_getArg(v___x_1816_, v___x_1786_);
lean_dec(v___x_1816_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_eq_1820_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_val_1821_);
v___y_1789_ = v___y_1812_;
v___y_1790_ = v_ty_1806_;
v___y_1791_ = v___y_1808_;
v___y_1792_ = v___y_1814_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1813_;
v___y_1795_ = v_c_1805_;
v___y_1796_ = v___y_1807_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1810_;
v_eq_1799_ = v___x_1822_;
v_val_1800_ = v___x_1823_;
goto v___jp_1788_;
}
}
else
{
lean_object* v___x_1824_; 
lean_dec(v___x_1816_);
v___x_1824_ = lean_box(0);
v___y_1789_ = v___y_1812_;
v___y_1790_ = v_ty_1806_;
v___y_1791_ = v___y_1808_;
v___y_1792_ = v___y_1814_;
v___y_1793_ = v___y_1811_;
v___y_1794_ = v___y_1813_;
v___y_1795_ = v_c_1805_;
v___y_1796_ = v___y_1807_;
v___y_1797_ = v___y_1809_;
v___y_1798_ = v___y_1810_;
v_eq_1799_ = v___x_1824_;
v_val_1800_ = v___x_1824_;
goto v___jp_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed(lean_object* v_x_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(v_x_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1(){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1853_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1854_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1));
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1));
v___x_1856_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed), 10, 0);
v___x_1857_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1853_, v___x_1854_, v___x_1855_, v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___boxed(lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3(){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1));
v___x_1887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6));
v___x_1888_ = l_Lean_addBuiltinDeclarationRanges(v___x_1886_, v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___boxed(lean_object* v_a_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1(){
_start:
{
lean_object* v___f_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___f_1921_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed), 10, 0);
v___x_1922_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1923_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3));
v___x_1924_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1));
v___x_1925_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1922_, v___x_1923_, v___x_1924_, v___f_1921_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___boxed(lean_object* v_a_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3(){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1));
v___x_1955_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6));
v___x_1956_ = l_Lean_addBuiltinDeclarationRanges(v___x_1954_, v___x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___boxed(lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg(){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg___boxed(lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(lean_object* v_00_u03b1_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___boxed(lean_object* v_00_u03b1_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(v_00_u03b1_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg(){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg___boxed(lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(lean_object* v_00_u03b1_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___boxed(lean_object* v_00_u03b1_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(v_00_u03b1_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1996_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(lean_object* v_opts_1997_, lean_object* v_opt_1998_){
_start:
{
lean_object* v_name_1999_; lean_object* v_defValue_2000_; lean_object* v_map_2001_; lean_object* v___x_2002_; 
v_name_1999_ = lean_ctor_get(v_opt_1998_, 0);
v_defValue_2000_ = lean_ctor_get(v_opt_1998_, 1);
v_map_2001_ = lean_ctor_get(v_opts_1997_, 0);
v___x_2002_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2001_, v_name_1999_);
if (lean_obj_tag(v___x_2002_) == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = lean_unbox(v_defValue_2000_);
return v___x_2003_;
}
else
{
lean_object* v_val_2004_; 
v_val_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2004_);
lean_dec_ref_known(v___x_2002_, 1);
if (lean_obj_tag(v_val_2004_) == 1)
{
uint8_t v_v_2005_; 
v_v_2005_ = lean_ctor_get_uint8(v_val_2004_, 0);
lean_dec_ref_known(v_val_2004_, 0);
return v_v_2005_;
}
else
{
uint8_t v___x_2006_; 
lean_dec(v_val_2004_);
v___x_2006_ = lean_unbox(v_defValue_2000_);
return v___x_2006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_2007_, lean_object* v_opt_2008_){
_start:
{
uint8_t v_res_2009_; lean_object* v_r_2010_; 
v_res_2009_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_opts_2007_, v_opt_2008_);
lean_dec_ref(v_opt_2008_);
lean_dec_ref(v_opts_2007_);
v_r_2010_ = lean_box(v_res_2009_);
return v_r_2010_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_box(1);
v___x_2012_ = l_Lean_MessageData_ofFormat(v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2));
v___x_2017_ = l_Lean_MessageData_ofFormat(v___x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(lean_object* v_x_2018_, lean_object* v_x_2019_){
_start:
{
if (lean_obj_tag(v_x_2019_) == 0)
{
return v_x_2018_;
}
else
{
lean_object* v_head_2020_; lean_object* v_tail_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2043_; 
v_head_2020_ = lean_ctor_get(v_x_2019_, 0);
v_tail_2021_ = lean_ctor_get(v_x_2019_, 1);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_x_2019_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2023_ = v_x_2019_;
v_isShared_2024_ = v_isSharedCheck_2043_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_tail_2021_);
lean_inc(v_head_2020_);
lean_dec(v_x_2019_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2043_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v_before_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2041_; 
v_before_2025_ = lean_ctor_get(v_head_2020_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_head_2020_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v_head_2020_, 1);
lean_dec(v_unused_2042_);
v___x_2027_ = v_head_2020_;
v_isShared_2028_ = v_isSharedCheck_2041_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_before_2025_);
lean_dec(v_head_2020_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2041_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 7);
lean_ctor_set(v___x_2027_, 1, v___x_2029_);
lean_ctor_set(v___x_2027_, 0, v_x_2018_);
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_x_2018_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2032_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3);
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 7);
lean_ctor_set(v___x_2023_, 1, v___x_2032_);
lean_ctor_set(v___x_2023_, 0, v___x_2031_);
v___x_2034_ = v___x_2023_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = l_Lean_MessageData_ofSyntax(v_before_2025_);
v___x_2036_ = l_Lean_indentD(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2034_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v_x_2018_ = v___x_2037_;
v_x_2019_ = v_tail_2021_;
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
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1));
v___x_2048_ = l_Lean_MessageData_ofFormat(v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(lean_object* v_msgData_2049_, lean_object* v_macroStack_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_options_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_options_2053_ = lean_ctor_get(v___y_2051_, 2);
v___x_2054_ = l_Lean_Elab_pp_macroStack;
v___x_2055_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_options_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
lean_dec(v_macroStack_2050_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v_msgData_2049_);
return v___x_2056_;
}
else
{
if (lean_obj_tag(v_macroStack_2050_) == 0)
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_msgData_2049_);
return v___x_2057_;
}
else
{
lean_object* v_head_2058_; lean_object* v_after_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2074_; 
v_head_2058_ = lean_ctor_get(v_macroStack_2050_, 0);
lean_inc(v_head_2058_);
v_after_2059_ = lean_ctor_get(v_head_2058_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_head_2058_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_head_2058_, 0);
lean_dec(v_unused_2075_);
v___x_2061_ = v_head_2058_;
v_isShared_2062_ = v_isSharedCheck_2074_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_after_2059_);
lean_dec(v_head_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2074_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_2062_ == 0)
{
lean_ctor_set_tag(v___x_2061_, 7);
lean_ctor_set(v___x_2061_, 1, v___x_2063_);
lean_ctor_set(v___x_2061_, 0, v_msgData_2049_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_msgData_2049_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_msgData_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2066_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_MessageData_ofSyntax(v_after_2059_);
v___x_2069_ = l_Lean_indentD(v___x_2068_);
v_msgData_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2070_, 0, v___x_2067_);
lean_ctor_set(v_msgData_2070_, 1, v___x_2069_);
v___x_2071_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(v_msgData_2070_, v_macroStack_2050_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2076_, lean_object* v_macroStack_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_2076_, v_macroStack_2077_, v___y_2078_);
lean_dec_ref(v___y_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(lean_object* v_msg_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_ref_2089_; lean_object* v___x_2090_; lean_object* v_a_2091_; lean_object* v_macroStack_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_ref_2089_ = lean_ctor_get(v___y_2086_, 5);
v___x_2090_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_2081_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
v_macroStack_2092_ = lean_ctor_get(v___y_2082_, 1);
v___x_2093_ = l_Lean_Elab_getBetterRef(v_ref_2089_, v_macroStack_2092_);
lean_inc(v_macroStack_2092_);
v___x_2094_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_a_2091_, v_macroStack_2092_, v___y_2086_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2093_);
lean_ctor_set(v___x_2099_, 1, v_a_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set_tag(v___x_2097_, 1);
lean_ctor_set(v___x_2097_, 0, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg___boxed(lean_object* v_msg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v_msg_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(lean_object* v_eq_2113_, lean_object* v_r_2114_, lean_object* v_p_2115_, lean_object* v_x_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_2113_);
if (lean_obj_tag(v___x_2124_) == 1)
{
lean_object* v_val_2125_; lean_object* v___x_2126_; 
v_val_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc_n(v_val_2125_, 2);
lean_dec_ref_known(v___x_2124_, 1);
lean_inc(v_p_2115_);
lean_inc(v_r_2114_);
v___x_2126_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(v_val_2125_, v_r_2114_, v_p_2115_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2151_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2151_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2151_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
uint8_t v___x_2131_; 
v___x_2131_ = lean_unbox(v_a_2127_);
lean_dec(v_a_2127_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
lean_del_object(v___x_2129_);
v___x_2132_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1);
v___x_2133_ = l_Lean_MessageData_ofSyntax(v_r_2114_);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3);
v___x_2136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_2125_);
lean_dec(v_val_2125_);
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
v___x_2139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2136_);
lean_ctor_set(v___x_2139_, 1, v___x_2138_);
v___x_2140_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = l_Lean_MessageData_ofSyntax(v_p_2115_);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7, &l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_2145_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
return v___x_2146_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
lean_dec(v_val_2125_);
lean_dec(v_p_2115_);
lean_dec(v_r_2114_);
v___x_2147_ = lean_box(0);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2147_);
v___x_2149_ = v___x_2129_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_val_2125_);
lean_dec(v_p_2115_);
lean_dec(v_r_2114_);
v_a_2152_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2126_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2126_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v___x_2160_; 
lean_dec(v___x_2124_);
lean_dec(v_p_2115_);
lean_dec(v_r_2114_);
v___x_2160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed(lean_object* v_eq_2161_, lean_object* v_r_2162_, lean_object* v_p_2163_, lean_object* v_x_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(v_eq_2161_, v_r_2162_, v_p_2163_, v_x_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec_ref(v_x_2164_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(lean_object* v_x_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2));
lean_inc(v_x_2180_);
v___x_2185_ = l_Lean_Syntax_isOfKind(v_x_2180_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_x_2180_);
v___x_2186_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; lean_object* v_eq_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2187_ = lean_unsigned_to_nat(2u);
v_eq_2188_ = l_Lean_Syntax_getArg(v_x_2180_, v___x_2187_);
v___x_2189_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1));
lean_inc(v_eq_2188_);
v___x_2190_ = l_Lean_Syntax_isOfKind(v_eq_2188_, v___x_2189_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
lean_dec(v_eq_2188_);
lean_dec(v_x_2180_);
v___x_2191_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; lean_object* v_r_2193_; lean_object* v___x_2194_; lean_object* v_p_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; 
v___x_2192_ = lean_unsigned_to_nat(1u);
v_r_2193_ = l_Lean_Syntax_getArg(v_x_2180_, v___x_2192_);
v___x_2194_ = lean_unsigned_to_nat(3u);
v_p_2195_ = l_Lean_Syntax_getArg(v_x_2180_, v___x_2194_);
lean_dec(v_x_2180_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2196_, 0, v_eq_2188_);
lean_closure_set(v___f_2196_, 1, v_r_2193_);
lean_closure_set(v___f_2196_, 2, v_p_2195_);
v___x_2197_ = l_Lean_Elab_Command_runTermElabM___redArg(v___f_2196_, v_a_2181_, v_a_2182_);
return v___x_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(lean_object* v_x_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(v_x_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(lean_object* v_00_u03b1_2203_, lean_object* v_msg_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v_msg_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___boxed(lean_object* v_00_u03b1_2213_, lean_object* v_msg_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(v_00_u03b1_2213_, v_msg_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(lean_object* v_msgData_2223_, lean_object* v_macroStack_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_2223_, v_macroStack_2224_, v___y_2229_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___boxed(lean_object* v_msgData_2233_, lean_object* v_macroStack_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(v_msgData_2233_, v_macroStack_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1(){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2251_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2252_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2));
v___x_2253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1));
v___x_2254_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed), 4, 0);
v___x_2255_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2251_, v___x_2252_, v___x_2253_, v___x_2254_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___boxed(lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3(){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1));
v___x_2285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6));
v___x_2286_ = l_Lean_addBuiltinDeclarationRanges(v___x_2284_, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___boxed(lean_object* v_a_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
return v_res_2288_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_box(0);
v___x_2293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1));
v___x_2294_ = l_Lean_mkConst(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(lean_object* v_e_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2301_; uint8_t v___x_2302_; uint8_t v___x_2303_; lean_object* v___x_2304_; 
v___x_2301_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2302_ = 1;
v___x_2303_ = 0;
v___x_2304_ = l_Lean_Meta_evalExpr___redArg(v___x_2301_, v_e_2295_, v___x_2302_, v___x_2303_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___boxed(lean_object* v_e_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(v_e_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2311_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0));
v___x_2314_ = l_Lean_stringToMessageData(v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(lean_object* v___x_2318_, lean_object* v___x_2319_, uint8_t v___x_2320_, lean_object* v___x_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2318_, v___x_2319_, v___x_2320_, v___x_2320_, v___x_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = 0;
v___x_2332_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_2331_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v___x_2333_; lean_object* v_a_2334_; lean_object* v___x_2335_; 
lean_dec_ref_known(v___x_2332_, 1);
v___x_2333_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_2330_, v___y_2325_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_n(v_a_2334_, 2);
lean_dec_ref(v___x_2333_);
v___x_2335_ = l_Lean_Meta_getMVars(v_a_2334_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = lean_array_get_size(v_a_2336_);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_nat_dec_eq(v___x_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec(v_a_2334_);
v___x_2340_ = lean_box(0);
v___x_2341_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(v_a_2336_, v___x_2340_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v_a_2336_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2349_; 
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v___x_2341_, 0);
lean_dec(v_unused_2350_);
v___x_2343_ = v___x_2341_;
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
else
{
lean_dec(v___x_2341_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_box(0);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_a_2351_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2341_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2341_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_object* v___x_2359_; 
lean_dec(v_a_2336_);
lean_inc(v_a_2334_);
v___x_2359_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(v_a_2334_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2375_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2375_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2375_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_unbox(v_a_2360_);
lean_dec(v_a_2360_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_del_object(v___x_2362_);
v___x_2365_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1);
v___x_2366_ = l_Lean_indentExpr(v_a_2334_);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_2369_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2370_;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
lean_dec(v_a_2334_);
v___x_2371_ = lean_box(0);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2371_);
v___x_2373_ = v___x_2362_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
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
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_a_2334_);
v_a_2376_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2359_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2359_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_a_2334_);
v_a_2384_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2335_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2335_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_dec(v_a_2330_);
return v___x_2332_;
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2329_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2329_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(lean_object* v___x_2400_, lean_object* v___x_2401_, lean_object* v___x_2402_, lean_object* v___x_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
uint8_t v___x_1792__boxed_2411_; lean_object* v_res_2412_; 
v___x_1792__boxed_2411_ = lean_unbox(v___x_2402_);
v_res_2412_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(v___x_2400_, v___x_2401_, v___x_1792__boxed_2411_, v___x_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
return v_res_2412_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2, &l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once, _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
v___x_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(lean_object* v_x_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1));
lean_inc(v_x_2421_);
v___x_2426_ = l_Lean_Syntax_isOfKind(v_x_2421_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
lean_dec(v_x_2421_);
v___x_2427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
return v___x_2427_;
}
else
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___f_2433_; lean_object* v___x_2434_; 
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = l_Lean_Syntax_getArg(v_x_2421_, v___x_2428_);
lean_dec(v_x_2421_);
v___x_2430_ = lean_obj_once(&l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2, &l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once, _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2);
v___x_2431_ = lean_box(0);
v___x_2432_ = lean_box(v___x_2426_);
v___f_2433_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2433_, 0, v___x_2429_);
lean_closure_set(v___f_2433_, 1, v___x_2430_);
lean_closure_set(v___f_2433_, 2, v___x_2432_);
lean_closure_set(v___f_2433_, 3, v___x_2431_);
v___x_2434_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2433_, v_a_2422_, v_a_2423_);
return v___x_2434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(lean_object* v_x_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(v_x_2435_, v_a_2436_, v_a_2437_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1(){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2448_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_2449_ = ((lean_object*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1));
v___x_2450_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1));
v___x_2451_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed), 4, 0);
v___x_2452_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2448_, v___x_2449_, v___x_2450_, v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___boxed(lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3(){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1));
v___x_2482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6));
v___x_2483_ = l_Lean_addBuiltinDeclarationRanges(v___x_2481_, v___x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___boxed(lean_object* v_a_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
return v_res_2485_;
}
}
lean_object* runtime_initialize_Init_Guard(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Guard(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
