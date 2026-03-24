// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Delab
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.MGoal
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_toSuperscriptString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___redArg();
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termSpred(_)"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 240, 91, 148, 237, 191, 255, 193)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__17_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20_value;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Notation"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__23_value),LEAN_SCALAR_PTR_LITERAL(66, 246, 126, 200, 193, 235, 124, 8)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__24_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PrettyPrinter"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(120, 167, 117, 148, 131, 202, 42, 4)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__27_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__29_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Macro"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__31_value),LEAN_SCALAR_PTR_LITERAL(168, 205, 218, 0, 241, 122, 66, 251)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__32_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__34_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__33_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__36_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__30_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__37_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__28_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__38_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__25_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__39_value)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__42_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45_value;
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__45_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46_value;
static lean_once_cell_t l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50_value;
static const lean_string_object l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51 = (const lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51_value;
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__0;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__3 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__4 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr.withMDataExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_delab___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mgoalHyp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 32, 213, 253, 69, 208, 115, 14)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 110, 128, 2, 249, 81, 25)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "✝"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__2_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed, .m_arity = 9, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__3_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mgoalStx"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_1),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 32, 213, 253, 69, 208, 115, 14)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__5_value),LEAN_SCALAR_PTR_LITERAL(192, 235, 142, 175, 247, 121, 9, 33)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 2, .m_data = "⊢ₛ"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "MGoalEntails"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 158, 147, 61, 120, 131, 143, 40)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 155, 62, 74, 112, 232, 12, 67)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 19, 244, 238, 51, 105, 65, 32)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 147, 60, 112, 241, 16, 26, 124)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(189, 150, 91, 41, 3, 103, 187, 5)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__4_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__8_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(235, 162, 5, 152, 35, 161, 128, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 24, 36, 109, 63, 35, 15, 26)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(255, 102, 110, 158, 71, 128, 63, 116)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__14_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(50, 96, 40, 212, 18, 230, 177, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__15_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(80, 221, 201, 140, 25, 135, 241, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value),LEAN_SCALAR_PTR_LITERAL(173, 239, 47, 15, 0, 87, 61, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__17_value),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(97, 189, 59, 243, 103, 237, 231, 154)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__18_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(83, 225, 48, 167, 37, 7, 6, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "delabMGoal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(99, 106, 62, 126, 26, 251, 92, 11)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "MGoalHypMarker"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 158, 147, 61, 120, 131, 143, 40)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_0),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 155, 62, 74, 112, 232, 12, 67)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 19, 244, 238, 51, 105, 65, 32)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_2),((lean_object*)&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 147, 60, 112, 241, 16, 26, 124)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 40, 245, 153, 183, 26, 90, 112)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "delabHypMarker"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__19_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 143, 163, 24, 122, 72, 121, 254)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(lean_object* v___y_1_){
_start:
{
lean_object* v_subExpr_3_; lean_object* v_expr_4_; lean_object* v___x_5_; 
v_subExpr_3_ = lean_ctor_get(v___y_1_, 3);
v_expr_4_ = lean_ctor_get(v_subExpr_3_, 0);
lean_inc_ref(v_expr_4_);
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_expr_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg___boxed(lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_6_);
lean_dec_ref(v___y_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_9_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___boxed(lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(lean_object* v_child_25_, lean_object* v_childIdx_26_, lean_object* v_x_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_subExpr_35_; lean_object* v_optionsPerPos_36_; lean_object* v_currNamespace_37_; lean_object* v_openDecls_38_; uint8_t v_inPattern_39_; lean_object* v_depth_40_; lean_object* v_pos_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_subExpr_35_ = lean_ctor_get(v___y_28_, 3);
v_optionsPerPos_36_ = lean_ctor_get(v___y_28_, 0);
v_currNamespace_37_ = lean_ctor_get(v___y_28_, 1);
v_openDecls_38_ = lean_ctor_get(v___y_28_, 2);
v_inPattern_39_ = lean_ctor_get_uint8(v___y_28_, sizeof(void*)*5);
v_depth_40_ = lean_ctor_get(v___y_28_, 4);
v_pos_41_ = lean_ctor_get(v_subExpr_35_, 1);
v___x_42_ = l_Lean_SubExpr_Pos_push(v_pos_41_, v_childIdx_26_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v_child_25_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
lean_inc(v_depth_40_);
lean_inc(v_openDecls_38_);
lean_inc(v_currNamespace_37_);
lean_inc(v_optionsPerPos_36_);
v___x_44_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_44_, 0, v_optionsPerPos_36_);
lean_ctor_set(v___x_44_, 1, v_currNamespace_37_);
lean_ctor_set(v___x_44_, 2, v_openDecls_38_);
lean_ctor_set(v___x_44_, 3, v___x_43_);
lean_ctor_set(v___x_44_, 4, v_depth_40_);
lean_ctor_set_uint8(v___x_44_, sizeof(void*)*5, v_inPattern_39_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
lean_inc_ref(v___y_30_);
lean_inc(v___y_29_);
v___x_45_ = lean_apply_7(v_x_27_, v___x_44_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, lean_box(0));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg___boxed(lean_object* v_child_46_, lean_object* v_childIdx_47_, lean_object* v_x_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v_child_46_, v_childIdx_47_, v_x_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(lean_object* v_x_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v___x_65_; lean_object* v_a_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_58_);
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_65_);
v___x_67_ = l_Lean_Expr_appArg_x21(v_a_66_);
lean_dec(v_a_66_);
v___x_68_ = lean_unsigned_to_nat(1u);
v___x_69_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v___x_67_, v___x_68_, v_x_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg___boxed(lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(lean_object* v_00_u03b1_79_, lean_object* v_x_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v_x_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed(lean_object* v_00_u03b1_89_, lean_object* v_x_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(v_00_u03b1_89_, v_x_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_98_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20));
v___x_142_ = l_String_toRawSubstring_x27(v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Array_mkArray0(lean_box(0));
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(lean_object* v_x_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3));
lean_inc(v_x_204_);
v___x_208_ = l_Lean_Syntax_isOfKind(v_x_204_, v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8));
lean_inc(v_x_204_);
v___x_210_ = l_Lean_Syntax_isOfKind(v_x_204_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10));
lean_inc(v_x_204_);
v___x_212_ = l_Lean_Syntax_isOfKind(v_x_204_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_213_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11));
v___x_214_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12));
lean_inc(v_x_204_);
v___x_215_ = l_Lean_Syntax_isOfKind(v_x_204_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14));
lean_inc(v_x_204_);
v___x_217_ = l_Lean_Syntax_isOfKind(v_x_204_, v___x_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec_ref(v___y_205_);
v___x_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_218_, 0, v_x_204_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = l_Lean_Syntax_getArg(v_x_204_, v___x_219_);
v___x_221_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16));
lean_inc(v___x_220_);
v___x_222_ = l_Lean_Syntax_isOfKind(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v___x_220_);
lean_dec_ref(v___y_205_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v_x_204_);
return v___x_223_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = l_Lean_Syntax_getArg(v___x_220_, v___x_224_);
lean_dec(v___x_220_);
v___x_226_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18));
lean_inc(v___x_225_);
v___x_227_ = l_Lean_Syntax_isOfKind(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v___x_225_);
lean_dec_ref(v___y_205_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v_x_204_);
return v___x_228_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_229_ = l_Lean_Syntax_getArg(v___x_225_, v___x_219_);
lean_dec(v___x_225_);
v___x_230_ = lean_box(0);
v___x_231_ = l_Lean_Syntax_matchesIdent(v___x_229_, v___x_230_);
lean_dec(v___x_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
lean_dec_ref(v___y_205_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v_x_204_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(3u);
v___x_234_ = l_Lean_Syntax_getArg(v_x_204_, v___x_233_);
lean_inc(v___x_234_);
v___x_235_ = l_Lean_Syntax_matchesNull(v___x_234_, v___x_224_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec(v___x_234_);
lean_dec_ref(v___y_205_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v_x_204_);
return v___x_236_;
}
else
{
lean_object* v_P_237_; lean_object* v___x_238_; 
v_P_237_ = l_Lean_Syntax_getArg(v_x_204_, v___x_224_);
lean_dec(v_x_204_);
lean_inc_ref(v___y_205_);
v___x_238_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_P_237_, v___y_205_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_266_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_266_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_266_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_266_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_ref_243_; lean_object* v_quotContext_244_; lean_object* v_currMacroScope_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v_ref_243_ = lean_ctor_get(v___y_205_, 5);
lean_inc(v_ref_243_);
v_quotContext_244_ = lean_ctor_get(v___y_205_, 10);
lean_inc(v_quotContext_244_);
v_currMacroScope_245_ = lean_ctor_get(v___y_205_, 11);
lean_inc(v_currMacroScope_245_);
lean_dec_ref(v___y_205_);
v___x_246_ = l_Lean_Syntax_getArg(v___x_234_, v___x_219_);
lean_dec(v___x_234_);
v___x_247_ = l_Lean_SourceInfo_fromRef(v_ref_243_, v___x_215_);
lean_dec(v_ref_243_);
v___x_248_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19));
lean_inc(v___x_247_);
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21);
v___x_251_ = l_Lean_addMacroScope(v_quotContext_244_, v___x_230_, v_currMacroScope_245_);
v___x_252_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40));
lean_inc(v___x_247_);
v___x_253_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_253_, 0, v___x_247_);
lean_ctor_set(v___x_253_, 1, v___x_250_);
lean_ctor_set(v___x_253_, 2, v___x_251_);
lean_ctor_set(v___x_253_, 3, v___x_252_);
lean_inc(v___x_247_);
v___x_254_ = l_Lean_Syntax_node1(v___x_247_, v___x_226_, v___x_253_);
lean_inc(v___x_247_);
v___x_255_ = l_Lean_Syntax_node2(v___x_247_, v___x_221_, v___x_249_, v___x_254_);
v___x_256_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41));
lean_inc(v___x_247_);
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_247_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43));
lean_inc(v___x_247_);
v___x_259_ = l_Lean_Syntax_node1(v___x_247_, v___x_258_, v___x_246_);
v___x_260_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44));
lean_inc(v___x_247_);
v___x_261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_247_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = l_Lean_Syntax_node5(v___x_247_, v___x_216_, v___x_255_, v_a_239_, v___x_257_, v___x_259_, v___x_261_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_262_);
v___x_264_ = v___x_241_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_dec(v___x_234_);
lean_dec_ref(v___y_205_);
return v___x_238_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = l_Lean_Syntax_getArg(v_x_204_, v___x_267_);
v___x_269_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46));
lean_inc(v___x_268_);
v___x_270_ = l_Lean_Syntax_isOfKind(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec(v___x_268_);
lean_dec_ref(v___y_205_);
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v_x_204_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = l_Lean_Syntax_getArg(v___x_268_, v___x_267_);
v___x_274_ = l_Lean_Syntax_matchesNull(v___x_273_, v___x_272_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec(v___x_268_);
lean_dec_ref(v___y_205_);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v_x_204_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v_b_277_; lean_object* v___x_278_; 
lean_dec(v_x_204_);
v___x_276_ = lean_unsigned_to_nat(3u);
v_b_277_ = l_Lean_Syntax_getArg(v___x_268_, v___x_276_);
lean_inc_ref(v___y_205_);
v___x_278_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_b_277_, v___y_205_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_300_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_300_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_300_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_300_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_ref_283_; lean_object* v___x_284_; lean_object* v_xs_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v_ref_283_ = lean_ctor_get(v___y_205_, 5);
lean_inc(v_ref_283_);
lean_dec_ref(v___y_205_);
v___x_284_ = l_Lean_Syntax_getArg(v___x_268_, v___x_272_);
lean_dec(v___x_268_);
v_xs_285_ = l_Lean_Syntax_getArgs(v___x_284_);
lean_dec(v___x_284_);
v___x_286_ = l_Lean_SourceInfo_fromRef(v_ref_283_, v___x_212_);
lean_dec(v_ref_283_);
lean_inc(v___x_286_);
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_213_);
v___x_288_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43));
v___x_289_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47);
v___x_290_ = l_Array_append___redArg(v___x_289_, v_xs_285_);
lean_dec_ref(v_xs_285_);
lean_inc(v___x_286_);
v___x_291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_291_, 0, v___x_286_);
lean_ctor_set(v___x_291_, 1, v___x_288_);
lean_ctor_set(v___x_291_, 2, v___x_290_);
lean_inc(v___x_286_);
v___x_292_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_292_, 0, v___x_286_);
lean_ctor_set(v___x_292_, 1, v___x_288_);
lean_ctor_set(v___x_292_, 2, v___x_289_);
v___x_293_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48));
lean_inc(v___x_286_);
v___x_294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_286_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
lean_inc(v___x_286_);
v___x_295_ = l_Lean_Syntax_node4(v___x_286_, v___x_269_, v___x_291_, v___x_292_, v___x_294_, v_a_279_);
v___x_296_ = l_Lean_Syntax_node2(v___x_286_, v___x_214_, v___x_287_, v___x_295_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_296_);
v___x_298_ = v___x_281_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
lean_dec(v___x_268_);
lean_dec_ref(v___y_205_);
return v___x_278_;
}
}
}
}
}
else
{
lean_object* v___x_301_; lean_object* v_t_302_; lean_object* v___x_303_; 
v___x_301_ = lean_unsigned_to_nat(3u);
v_t_302_ = l_Lean_Syntax_getArg(v_x_204_, v___x_301_);
lean_inc_ref(v___y_205_);
v___x_303_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_t_302_, v___y_205_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_305_; lean_object* v_e_306_; lean_object* v___x_307_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
v___x_305_ = lean_unsigned_to_nat(5u);
v_e_306_ = l_Lean_Syntax_getArg(v_x_204_, v___x_305_);
lean_inc_ref(v___y_205_);
v___x_307_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_e_306_, v___y_205_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_326_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_326_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_326_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_326_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_ref_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v_ref_312_ = lean_ctor_get(v___y_205_, 5);
lean_inc(v_ref_312_);
lean_dec_ref(v___y_205_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = l_Lean_Syntax_getArg(v_x_204_, v___x_313_);
lean_dec(v_x_204_);
v___x_315_ = l_Lean_SourceInfo_fromRef(v_ref_312_, v___x_210_);
lean_dec(v_ref_312_);
v___x_316_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49));
lean_inc(v___x_315_);
v___x_317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50));
lean_inc(v___x_315_);
v___x_319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_315_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51));
lean_inc(v___x_315_);
v___x_321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_315_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_Syntax_node6(v___x_315_, v___x_211_, v___x_317_, v___x_314_, v___x_319_, v_a_304_, v___x_321_, v_a_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_322_);
v___x_324_ = v___x_310_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_dec(v_a_304_);
lean_dec_ref(v___y_205_);
lean_dec(v_x_204_);
return v___x_307_;
}
}
else
{
lean_dec_ref(v___y_205_);
lean_dec(v_x_204_);
return v___x_303_;
}
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = l_Lean_Syntax_getArg(v_x_204_, v___x_327_);
v___x_329_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16));
lean_inc(v___x_328_);
v___x_330_ = l_Lean_Syntax_isOfKind(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v___x_328_);
lean_dec_ref(v___y_205_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_x_204_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_332_ = lean_unsigned_to_nat(1u);
v___x_333_ = l_Lean_Syntax_getArg(v___x_328_, v___x_332_);
lean_dec(v___x_328_);
v___x_334_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18));
lean_inc(v___x_333_);
v___x_335_ = l_Lean_Syntax_isOfKind(v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v___x_333_);
lean_dec_ref(v___y_205_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_x_204_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_337_ = l_Lean_Syntax_getArg(v___x_333_, v___x_327_);
lean_dec(v___x_333_);
v___x_338_ = lean_box(0);
v___x_339_ = l_Lean_Syntax_matchesIdent(v___x_337_, v___x_338_);
lean_dec(v___x_337_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; 
lean_dec_ref(v___y_205_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v_x_204_);
return v___x_340_;
}
else
{
lean_object* v_P_341_; lean_object* v___x_342_; 
v_P_341_ = l_Lean_Syntax_getArg(v_x_204_, v___x_332_);
lean_dec(v_x_204_);
lean_inc_ref(v___y_205_);
v___x_342_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_P_341_, v___y_205_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_365_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_365_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_365_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_365_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_ref_347_; lean_object* v_quotContext_348_; lean_object* v_currMacroScope_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v_ref_347_ = lean_ctor_get(v___y_205_, 5);
lean_inc(v_ref_347_);
v_quotContext_348_ = lean_ctor_get(v___y_205_, 10);
lean_inc(v_quotContext_348_);
v_currMacroScope_349_ = lean_ctor_get(v___y_205_, 11);
lean_inc(v_currMacroScope_349_);
lean_dec_ref(v___y_205_);
v___x_350_ = l_Lean_SourceInfo_fromRef(v_ref_347_, v___x_208_);
lean_dec(v_ref_347_);
v___x_351_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19));
lean_inc(v___x_350_);
v___x_352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21);
v___x_354_ = l_Lean_addMacroScope(v_quotContext_348_, v___x_338_, v_currMacroScope_349_);
v___x_355_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40));
lean_inc(v___x_350_);
v___x_356_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_356_, 0, v___x_350_);
lean_ctor_set(v___x_356_, 1, v___x_353_);
lean_ctor_set(v___x_356_, 2, v___x_354_);
lean_ctor_set(v___x_356_, 3, v___x_355_);
lean_inc(v___x_350_);
v___x_357_ = l_Lean_Syntax_node1(v___x_350_, v___x_334_, v___x_356_);
lean_inc(v___x_350_);
v___x_358_ = l_Lean_Syntax_node2(v___x_350_, v___x_329_, v___x_352_, v___x_357_);
v___x_359_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44));
lean_inc(v___x_350_);
v___x_360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_350_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_Syntax_node3(v___x_350_, v___x_209_, v___x_358_, v_a_343_, v___x_360_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_361_);
v___x_363_ = v___x_345_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
else
{
lean_dec_ref(v___y_205_);
return v___x_342_;
}
}
}
}
}
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
lean_dec_ref(v___y_205_);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = l_Lean_Syntax_getArg(v_x_204_, v___x_366_);
lean_dec(v_x_204_);
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___boxed(lean_object* v_x_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_x_369_, v___y_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(lean_object* v_x_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_a_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_381_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_374_);
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref(v___x_381_);
v___x_383_ = l_Lean_Expr_appFn_x21(v_a_382_);
lean_dec(v_a_382_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v___x_383_, v___x_384_, v_x_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg___boxed(lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v_x_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_394_;
}
}
static lean_object* _init_l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_instMonadEIO(lean_box(0));
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg(lean_object* v_inst_400_, lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_toApplicative_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_473_; 
v___x_409_ = lean_obj_once(&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__0, &l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__0);
v___x_410_ = l_StateRefT_x27_instMonad___redArg(v___x_409_);
v_toApplicative_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v___x_410_, 1);
lean_dec(v_unused_474_);
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_473_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_toApplicative_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_473_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v_toFunctor_415_; lean_object* v_toSeq_416_; lean_object* v_toSeqLeft_417_; lean_object* v_toSeqRight_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_471_; 
v_toFunctor_415_ = lean_ctor_get(v_toApplicative_411_, 0);
v_toSeq_416_ = lean_ctor_get(v_toApplicative_411_, 2);
v_toSeqLeft_417_ = lean_ctor_get(v_toApplicative_411_, 3);
v_toSeqRight_418_ = lean_ctor_get(v_toApplicative_411_, 4);
v_isSharedCheck_471_ = !lean_is_exclusive(v_toApplicative_411_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v_toApplicative_411_, 1);
lean_dec(v_unused_472_);
v___x_420_ = v_toApplicative_411_;
v_isShared_421_ = v_isSharedCheck_471_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_toSeqRight_418_);
lean_inc(v_toSeqLeft_417_);
lean_inc(v_toSeq_416_);
lean_inc(v_toFunctor_415_);
lean_dec(v_toApplicative_411_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_471_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___f_422_; lean_object* v___f_423_; lean_object* v___f_424_; lean_object* v___f_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___f_428_; lean_object* v___f_429_; lean_object* v___x_431_; 
v___f_422_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__1));
v___f_423_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__2));
lean_inc_ref(v_toFunctor_415_);
v___f_424_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_424_, 0, v_toFunctor_415_);
v___f_425_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_425_, 0, v_toFunctor_415_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___f_424_);
lean_ctor_set(v___x_426_, 1, v___f_425_);
v___f_427_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_427_, 0, v_toSeqRight_418_);
v___f_428_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_428_, 0, v_toSeqLeft_417_);
v___f_429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_429_, 0, v_toSeq_416_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 4, v___f_427_);
lean_ctor_set(v___x_420_, 3, v___f_428_);
lean_ctor_set(v___x_420_, 2, v___f_429_);
lean_ctor_set(v___x_420_, 1, v___f_422_);
lean_ctor_set(v___x_420_, 0, v___x_426_);
v___x_431_ = v___x_420_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___f_422_);
lean_ctor_set(v_reuseFailAlloc_470_, 2, v___f_429_);
lean_ctor_set(v_reuseFailAlloc_470_, 3, v___f_428_);
lean_ctor_set(v_reuseFailAlloc_470_, 4, v___f_427_);
v___x_431_ = v_reuseFailAlloc_470_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___f_423_);
lean_ctor_set(v___x_413_, 0, v___x_431_);
v___x_433_ = v___x_413_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___f_423_);
v___x_433_ = v_reuseFailAlloc_469_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_434_; lean_object* v_toApplicative_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_467_; 
v___x_434_ = l_StateRefT_x27_instMonad___redArg(v___x_433_);
v_toApplicative_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_434_, 1);
lean_dec(v_unused_468_);
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_467_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_toApplicative_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_467_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v_toFunctor_439_; lean_object* v_toSeq_440_; lean_object* v_toSeqLeft_441_; lean_object* v_toSeqRight_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_465_; 
v_toFunctor_439_ = lean_ctor_get(v_toApplicative_435_, 0);
v_toSeq_440_ = lean_ctor_get(v_toApplicative_435_, 2);
v_toSeqLeft_441_ = lean_ctor_get(v_toApplicative_435_, 3);
v_toSeqRight_442_ = lean_ctor_get(v_toApplicative_435_, 4);
v_isSharedCheck_465_ = !lean_is_exclusive(v_toApplicative_435_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_toApplicative_435_, 1);
lean_dec(v_unused_466_);
v___x_444_ = v_toApplicative_435_;
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_toSeqRight_442_);
lean_inc(v_toSeqLeft_441_);
lean_inc(v_toSeq_440_);
lean_inc(v_toFunctor_439_);
lean_dec(v_toApplicative_435_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_465_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___f_446_; lean_object* v___f_447_; lean_object* v___f_448_; lean_object* v___f_449_; lean_object* v___x_450_; lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v___f_453_; lean_object* v___x_455_; 
v___f_446_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__3));
v___f_447_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___closed__4));
lean_inc_ref(v_toFunctor_439_);
v___f_448_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_448_, 0, v_toFunctor_439_);
v___f_449_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_449_, 0, v_toFunctor_439_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___f_448_);
lean_ctor_set(v___x_450_, 1, v___f_449_);
v___f_451_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_451_, 0, v_toSeqRight_442_);
v___f_452_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_452_, 0, v_toSeqLeft_441_);
v___f_453_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_453_, 0, v_toSeq_440_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 4, v___f_451_);
lean_ctor_set(v___x_444_, 3, v___f_452_);
lean_ctor_set(v___x_444_, 2, v___f_453_);
lean_ctor_set(v___x_444_, 1, v___f_446_);
lean_ctor_set(v___x_444_, 0, v___x_450_);
v___x_455_ = v___x_444_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___f_446_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v___f_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v___f_452_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v___f_451_);
v___x_455_ = v_reuseFailAlloc_464_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_457_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v___f_447_);
lean_ctor_set(v___x_437_, 0, v___x_455_);
v___x_457_ = v___x_437_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___f_447_);
v___x_457_ = v_reuseFailAlloc_463_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_38363__overap_461_; lean_object* v___x_462_; 
v___x_458_ = l_StateRefT_x27_instMonad___redArg(v___x_457_);
v___x_459_ = l_ReaderT_instMonad___redArg(v___x_458_);
v___x_460_ = l_instInhabitedOfMonad___redArg(v___x_459_, v_inst_400_);
v___x_38363__overap_461_ = lean_panic_fn(v___x_460_, v_msg_401_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
lean_inc(v___y_403_);
lean_inc_ref(v___y_402_);
v___x_462_ = lean_apply_7(v___x_38363__overap_461_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
return v___x_462_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg___boxed(lean_object* v_inst_475_, lean_object* v_msg_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg(v_inst_475_, v_msg_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_484_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_488_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__2));
v___x_489_ = lean_unsigned_to_nat(33u);
v___x_490_ = lean_unsigned_to_nat(114u);
v___x_491_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__1));
v___x_492_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__0));
v___x_493_ = l_mkPanicMessageWithDecl(v___x_492_, v___x_491_, v___x_490_, v___x_489_, v___x_488_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg(lean_object* v_inst_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; lean_object* v_a_504_; 
v___x_503_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_496_);
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
if (lean_obj_tag(v_a_504_) == 10)
{
lean_object* v_subExpr_505_; lean_object* v_expr_506_; lean_object* v_optionsPerPos_507_; lean_object* v_currNamespace_508_; lean_object* v_openDecls_509_; uint8_t v_inPattern_510_; lean_object* v_depth_511_; lean_object* v_pos_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_inst_494_);
v_subExpr_505_ = lean_ctor_get(v___y_496_, 3);
v_expr_506_ = lean_ctor_get(v_a_504_, 1);
lean_inc_ref(v_expr_506_);
lean_dec_ref(v_a_504_);
v_optionsPerPos_507_ = lean_ctor_get(v___y_496_, 0);
v_currNamespace_508_ = lean_ctor_get(v___y_496_, 1);
v_openDecls_509_ = lean_ctor_get(v___y_496_, 2);
v_inPattern_510_ = lean_ctor_get_uint8(v___y_496_, sizeof(void*)*5);
v_depth_511_ = lean_ctor_get(v___y_496_, 4);
v_pos_512_ = lean_ctor_get(v_subExpr_505_, 1);
lean_inc(v_pos_512_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v_expr_506_);
lean_ctor_set(v___x_513_, 1, v_pos_512_);
lean_inc(v_depth_511_);
lean_inc(v_openDecls_509_);
lean_inc(v_currNamespace_508_);
lean_inc(v_optionsPerPos_507_);
v___x_514_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_514_, 0, v_optionsPerPos_507_);
lean_ctor_set(v___x_514_, 1, v_currNamespace_508_);
lean_ctor_set(v___x_514_, 2, v_openDecls_509_);
lean_ctor_set(v___x_514_, 3, v___x_513_);
lean_ctor_set(v___x_514_, 4, v_depth_511_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5, v_inPattern_510_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
v___x_515_ = lean_apply_7(v_x_495_, v___x_514_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, lean_box(0));
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_a_504_);
lean_dec_ref(v_x_495_);
v___x_516_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__3, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__3_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___closed__3);
v___x_517_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg(v_inst_494_, v___x_516_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg___boxed(lean_object* v_inst_518_, lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg(v_inst_518_, v_x_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(lean_object* v_t_528_, lean_object* v_k_529_, lean_object* v_fallback_530_){
_start:
{
if (lean_obj_tag(v_t_528_) == 0)
{
lean_object* v_k_531_; lean_object* v_v_532_; lean_object* v_l_533_; lean_object* v_r_534_; uint8_t v___x_535_; 
v_k_531_ = lean_ctor_get(v_t_528_, 1);
v_v_532_ = lean_ctor_get(v_t_528_, 2);
v_l_533_ = lean_ctor_get(v_t_528_, 3);
v_r_534_ = lean_ctor_get(v_t_528_, 4);
v___x_535_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_529_, v_k_531_);
switch(v___x_535_)
{
case 0:
{
v_t_528_ = v_l_533_;
goto _start;
}
case 1:
{
lean_inc(v_v_532_);
return v_v_532_;
}
default: 
{
v_t_528_ = v_r_534_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_530_);
return v_fallback_530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg___boxed(lean_object* v_t_538_, lean_object* v_k_539_, lean_object* v_fallback_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_t_538_, v_k_539_, v_fallback_540_);
lean_dec(v_fallback_540_);
lean_dec(v_k_539_);
lean_dec(v_t_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed(lean_object* v_acc_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(v_acc_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(lean_object* v_acc_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v_a_561_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_671_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_671_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_671_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_671_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; 
lean_inc(v_a_569_);
v___x_573_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_a_569_);
if (lean_obj_tag(v___x_573_) == 1)
{
lean_object* v___x_575_; 
lean_dec_ref(v___x_573_);
lean_dec(v_a_569_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_acc_560_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_acc_560_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v___x_577_; 
lean_dec(v___x_573_);
lean_inc(v_a_569_);
v___x_577_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_a_569_);
if (lean_obj_tag(v___x_577_) == 1)
{
lean_object* v_snd_578_; lean_object* v_val_579_; lean_object* v_fst_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_661_; 
lean_dec(v_a_569_);
v_snd_578_ = lean_ctor_get(v_acc_560_, 1);
lean_inc(v_snd_578_);
v_val_579_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_579_);
lean_dec_ref(v___x_577_);
v_fst_580_ = lean_ctor_get(v_acc_560_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_acc_560_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_acc_560_, 1);
lean_dec(v_unused_662_);
v___x_582_ = v_acc_560_;
v_isShared_583_ = v_isSharedCheck_661_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_fst_580_);
lean_dec(v_acc_560_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_661_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_660_; 
v_fst_584_ = lean_ctor_get(v_snd_578_, 0);
v_snd_585_ = lean_ctor_get(v_snd_578_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_snd_578_);
if (v_isSharedCheck_660_ == 0)
{
v___x_587_ = v_snd_578_;
v_isShared_588_ = v_isSharedCheck_660_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_inc(v_fst_584_);
lean_dec(v_snd_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_660_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___y_590_; lean_object* v_accessibles_591_; lean_object* v_inaccessibles_592_; lean_object* v_name_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v_val_646_; 
v_name_603_ = lean_ctor_get(v_val_579_, 0);
lean_inc(v_name_603_);
lean_dec(v_val_579_);
lean_inc(v_name_603_);
v___x_604_ = lean_erase_macro_scopes(v_name_603_);
v___x_605_ = l_Lean_Name_hasMacroScopes(v_name_603_);
lean_dec(v_name_603_);
if (v___x_605_ == 0)
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_fst_580_, v___x_604_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; 
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___x_655_);
v_val_646_ = v_val_656_;
goto v___jp_645_;
}
else
{
lean_object* v___x_657_; 
lean_dec(v___x_655_);
v___x_657_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_604_);
v_fst_607_ = v___x_657_;
v_snd_608_ = v___x_604_;
goto v___jp_606_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_fst_584_, v___x_604_, v___x_658_);
v_val_646_ = v___x_659_;
goto v___jp_645_;
}
v___jp_589_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_593_ = lean_array_push(v_snd_585_, v___y_590_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_593_);
lean_ctor_set(v___x_587_, 0, v_inaccessibles_592_);
v___x_595_ = v___x_587_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_inaccessibles_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_593_);
v___x_595_ = v_reuseFailAlloc_602_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 1, v___x_595_);
lean_ctor_set(v___x_582_, 0, v_accessibles_591_);
v___x_597_ = v___x_582_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_accessibles_591_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_601_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_599_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_597_);
v___x_599_ = v___x_571_;
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
}
}
v___jp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
v___x_610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0));
v___x_611_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg(v___x_609_, v___x_610_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_613_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref(v___x_611_);
lean_inc_ref(v_a_565_);
v___x_613_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_612_, v_a_565_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v_ref_615_; lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref(v___x_613_);
v_ref_615_ = lean_ctor_get(v_a_565_, 5);
v___x_616_ = lean_mk_syntax_ident(v_snd_608_);
v___x_617_ = 0;
v___x_618_ = l_Lean_SourceInfo_fromRef(v_ref_615_, v___x_617_);
v___x_619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3));
v___x_620_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41));
lean_inc(v___x_618_);
v___x_621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_618_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = l_Lean_Syntax_node3(v___x_618_, v___x_619_, v___x_616_, v___x_621_, v_a_614_);
if (v___x_605_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_604_, v_fst_607_, v_fst_580_);
v___y_590_ = v___x_622_;
v_accessibles_591_ = v___x_623_;
v_inaccessibles_592_ = v_fst_584_;
goto v___jp_589_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_604_, v_fst_607_, v_fst_584_);
v___y_590_ = v___x_622_;
v_accessibles_591_ = v_fst_580_;
v_inaccessibles_592_ = v___x_624_;
goto v___jp_589_;
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_snd_608_);
lean_dec(v_fst_607_);
lean_dec(v___x_604_);
lean_del_object(v___x_587_);
lean_dec(v_snd_585_);
lean_dec(v_fst_584_);
lean_del_object(v___x_582_);
lean_dec(v_fst_580_);
lean_del_object(v___x_571_);
v_a_625_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_613_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_613_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec(v_snd_608_);
lean_dec(v_fst_607_);
lean_dec(v___x_604_);
lean_del_object(v___x_587_);
lean_dec(v_snd_585_);
lean_dec(v_fst_584_);
lean_del_object(v___x_582_);
lean_dec(v_fst_580_);
lean_del_object(v___x_571_);
v_a_633_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_611_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_611_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
v___jp_641_:
{
lean_object* v___x_644_; 
lean_inc(v___x_604_);
v___x_644_ = lean_name_append_after(v___x_604_, v___y_643_);
v_fst_607_ = v___y_642_;
v_snd_608_ = v___x_644_;
goto v___jp_606_;
}
v___jp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_add(v_val_646_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_nat_dec_eq(v_val_646_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4));
v___x_652_ = l_Nat_toSuperscriptString(v_val_646_);
v___x_653_ = lean_string_append(v___x_651_, v___x_652_);
lean_dec_ref(v___x_652_);
v___y_642_ = v___x_648_;
v___y_643_ = v___x_653_;
goto v___jp_641_;
}
else
{
lean_object* v___x_654_; 
lean_dec(v_val_646_);
v___x_654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4));
v___y_642_ = v___x_648_;
v___y_643_ = v___x_654_;
goto v___jp_641_;
}
}
}
}
}
else
{
lean_object* v___x_663_; 
lean_dec(v___x_577_);
lean_del_object(v___x_571_);
v___x_663_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_a_569_);
lean_dec(v_a_569_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; 
lean_dec_ref(v_acc_560_);
v___x_664_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec_ref(v___x_663_);
v___x_665_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed), 8, 1);
lean_closure_set(v___x_665_, 0, v_acc_560_);
v___x_666_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_665_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed), 8, 1);
lean_closure_set(v___x_668_, 0, v_a_667_);
v___x_669_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed), 9, 2);
lean_closure_set(v___x_669_, 0, lean_box(0));
lean_closure_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v___x_669_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
return v___x_670_;
}
else
{
return v___x_666_;
}
}
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_acc_560_);
v_a_672_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_568_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_568_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(lean_object* v_00_u03b1_680_, lean_object* v_inst_681_, lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___redArg(v_inst_681_, v_msg_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___boxed(lean_object* v_00_u03b1_691_, lean_object* v_inst_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(v_00_u03b1_691_, v_inst_692_, v_msg_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(lean_object* v_00_u03b1_702_, lean_object* v_inst_703_, lean_object* v_x_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___redArg(v_inst_703_, v_x_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___boxed(lean_object* v_00_u03b1_713_, lean_object* v_inst_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(v_00_u03b1_713_, v_inst_714_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
lean_inc_ref(v___y_729_);
v___x_732_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_x_724_, v___y_729_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___boxed(lean_object* v_x_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(v_x_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3(lean_object* v_00_u03b4_742_, lean_object* v_t_743_, lean_object* v_k_744_, lean_object* v_fallback_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_t_743_, v_k_744_, v_fallback_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___boxed(lean_object* v_00_u03b4_747_, lean_object* v_t_748_, lean_object* v_k_749_, lean_object* v_fallback_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3(v_00_u03b4_747_, v_t_748_, v_k_749_, v_fallback_750_);
lean_dec(v_fallback_750_);
lean_dec(v_k_749_);
lean_dec(v_t_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(lean_object* v_00_u03b1_752_, lean_object* v_child_753_, lean_object* v_childIdx_754_, lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v_child_753_, v_childIdx_754_, v_x_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___boxed(lean_object* v_00_u03b1_764_, lean_object* v_child_765_, lean_object* v_childIdx_766_, lean_object* v_x_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(v_00_u03b1_764_, v_child_765_, v_childIdx_766_, v_x_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(lean_object* v_00_u03b1_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v_x_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___boxed(lean_object* v_00_u03b1_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(v_00_u03b1_786_, v_x_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_867_; lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_867_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v_a_815_);
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = lean_unsigned_to_nat(3u);
v___x_870_ = l_Lean_Expr_getAppNumArgs(v_a_868_);
lean_dec(v_a_868_);
v___x_871_ = lean_nat_dec_le(v___x_869_, v___x_870_);
lean_dec(v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
if (lean_obj_tag(v___x_872_) == 0)
{
lean_dec_ref(v___x_872_);
goto v___jp_822_;
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
else
{
goto v___jp_822_;
}
v___jp_822_:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4));
v___x_824_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v___x_823_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v_snd_826_; lean_object* v_snd_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_857_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref(v___x_824_);
v_snd_826_ = lean_ctor_get(v_a_825_, 1);
lean_inc(v_snd_826_);
lean_dec(v_a_825_);
v_snd_827_ = lean_ctor_get(v_snd_826_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_snd_826_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v_snd_826_, 0);
lean_dec(v_unused_858_);
v___x_829_ = v_snd_826_;
v_isShared_830_ = v_isSharedCheck_857_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_snd_827_);
lean_dec(v_snd_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_857_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0));
v___x_832_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_831_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_832_);
lean_inc_ref(v_a_819_);
v___x_834_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_833_, v_a_819_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_856_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_856_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_856_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_856_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v_ref_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v_ref_839_ = lean_ctor_get(v_a_819_, 5);
v___x_840_ = 0;
v___x_841_ = l_Lean_SourceInfo_fromRef(v_ref_839_, v___x_840_);
v___x_842_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6));
v___x_843_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43));
v___x_844_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47);
v___x_845_ = l_Array_reverse___redArg(v_snd_827_);
v___x_846_ = l_Array_append___redArg(v___x_844_, v___x_845_);
lean_dec_ref(v___x_845_);
lean_inc(v___x_841_);
v___x_847_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_847_, 0, v___x_841_);
lean_ctor_set(v___x_847_, 1, v___x_843_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7));
lean_inc(v___x_841_);
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 2);
lean_ctor_set(v___x_829_, 1, v___x_848_);
lean_ctor_set(v___x_829_, 0, v___x_841_);
v___x_850_ = v___x_829_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_855_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_Syntax_node3(v___x_841_, v___x_842_, v___x_847_, v___x_850_, v_a_835_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_851_);
v___x_853_ = v___x_837_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_del_object(v___x_829_);
lean_dec(v_snd_827_);
return v___x_834_;
}
}
else
{
lean_del_object(v___x_829_);
lean_dec(v_snd_827_);
return v___x_832_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_a_859_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_824_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_824_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___boxed(lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1(){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_945_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_946_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2));
v___x_947_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21));
v___x_948_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___boxed), 7, 0);
v___x_949_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_945_, v___x_946_, v___x_947_, v___x_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___boxed(lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1();
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0));
v___x_960_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_959_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
lean_inc_ref(v_a_956_);
v___x_962_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_961_, v_a_956_);
return v___x_962_;
}
else
{
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___boxed(lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1(){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_983_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1));
v___x_985_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3));
v___x_986_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___boxed), 7, 0);
v___x_987_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_983_, v___x_984_, v___x_985_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___boxed(lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1();
return v_res_989_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(builtin);
}
#ifdef __cplusplus
}
#endif
