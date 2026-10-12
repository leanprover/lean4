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
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Lean.PrettyPrinter.Delaborator.SubExpr.withMDataExpr"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1_value;
static const lean_string_object l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2 = (const lean_object*)&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(lean_object* v___y_1_){
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
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1_ = stack[0].m_obj;
lean_object* v_res_6_;
v_res_6_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_1_);
stack->m_obj
 = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg___boxed(lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_7_);
lean_dec_ref(v___y_7_);
return v_res_9_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_10_);
return v___x_17_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_10_ = stack[0].m_obj;
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v_res_18_;
v_res_18_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___boxed(lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0(v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_26_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(lean_object* v_child_27_, lean_object* v_childIdx_28_, lean_object* v_x_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_subExpr_37_; lean_object* v_optionsPerPos_38_; lean_object* v_currNamespace_39_; lean_object* v_openDecls_40_; uint8_t v_inPattern_41_; lean_object* v_depth_42_; lean_object* v_lctxInitIndices_43_; lean_object* v_pos_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_subExpr_37_ = lean_ctor_get(v___y_30_, 3);
v_optionsPerPos_38_ = lean_ctor_get(v___y_30_, 0);
v_currNamespace_39_ = lean_ctor_get(v___y_30_, 1);
v_openDecls_40_ = lean_ctor_get(v___y_30_, 2);
v_inPattern_41_ = lean_ctor_get_uint8(v___y_30_, sizeof(void*)*6);
v_depth_42_ = lean_ctor_get(v___y_30_, 4);
v_lctxInitIndices_43_ = lean_ctor_get(v___y_30_, 5);
v_pos_44_ = lean_ctor_get(v_subExpr_37_, 1);
v___x_45_ = l_Lean_SubExpr_Pos_push(v_pos_44_, v_childIdx_28_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_child_27_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
lean_inc(v_lctxInitIndices_43_);
lean_inc(v_depth_42_);
lean_inc(v_openDecls_40_);
lean_inc(v_currNamespace_39_);
lean_inc(v_optionsPerPos_38_);
v___x_47_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_47_, 0, v_optionsPerPos_38_);
lean_ctor_set(v___x_47_, 1, v_currNamespace_39_);
lean_ctor_set(v___x_47_, 2, v_openDecls_40_);
lean_ctor_set(v___x_47_, 3, v___x_46_);
lean_ctor_set(v___x_47_, 4, v_depth_42_);
lean_ctor_set(v___x_47_, 5, v_lctxInitIndices_43_);
lean_ctor_set_uint8(v___x_47_, sizeof(void*)*6, v_inPattern_41_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
lean_inc(v___y_31_);
v___x_48_ = lean_apply_7(v_x_29_, v___x_47_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, lean_box(0));
return v___x_48_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_child_27_ = stack[0].m_obj;
lean_object* v_childIdx_28_ = stack[1].m_obj;
lean_object* v_x_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v___y_32_ = stack[5].m_obj;
lean_object* v___y_33_ = stack[6].m_obj;
lean_object* v___y_34_ = stack[7].m_obj;
lean_object* v___y_35_ = stack[8].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v_child_27_, v_childIdx_28_, v_x_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg___boxed(lean_object* v_child_50_, lean_object* v_childIdx_51_, lean_object* v_x_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v_child_50_, v_childIdx_51_, v_x_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_60_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(lean_object* v_x_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; lean_object* v_a_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_69_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_62_);
v_a_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc(v_a_70_);
lean_dec_ref(v___x_69_);
v___x_71_ = l_Lean_Expr_appArg_x21(v_a_70_);
lean_dec(v_a_70_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v___x_71_, v___x_72_, v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_61_ = stack[0].m_obj;
lean_object* v___y_62_ = stack[1].m_obj;
lean_object* v___y_63_ = stack[2].m_obj;
lean_object* v___y_64_ = stack[3].m_obj;
lean_object* v___y_65_ = stack[4].m_obj;
lean_object* v___y_66_ = stack[5].m_obj;
lean_object* v___y_67_ = stack[6].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v_x_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg___boxed(lean_object* v_x_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v_x_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_83_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(lean_object* v_00_u03b1_84_, lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v_x_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v___y_91_ = stack[7].m_obj;
lean_object* v_res_94_;
v_res_94_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(lean_box(0), v_x_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed(lean_object* v_00_u03b1_95_, lean_object* v_x_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4(v_00_u03b1_95_, v_x_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
return v_res_104_;
}
}
static lean_object* _init_l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_instMonadEIO___redArg();
return v___x_105_;
}
}
lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_toApplicative_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_183_; 
v___x_118_ = lean_obj_once(&l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0, &l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0_once, _init_l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__0);
v___x_119_ = l_StateRefT_x27_instMonad___redArg(v___x_118_);
v_toApplicative_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_119_, 1);
lean_dec(v_unused_184_);
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_183_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_toApplicative_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_183_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_toFunctor_124_; lean_object* v_toSeq_125_; lean_object* v_toSeqLeft_126_; lean_object* v_toSeqRight_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_181_; 
v_toFunctor_124_ = lean_ctor_get(v_toApplicative_120_, 0);
v_toSeq_125_ = lean_ctor_get(v_toApplicative_120_, 2);
v_toSeqLeft_126_ = lean_ctor_get(v_toApplicative_120_, 3);
v_toSeqRight_127_ = lean_ctor_get(v_toApplicative_120_, 4);
v_isSharedCheck_181_ = !lean_is_exclusive(v_toApplicative_120_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_toApplicative_120_, 1);
lean_dec(v_unused_182_);
v___x_129_ = v_toApplicative_120_;
v_isShared_130_ = v_isSharedCheck_181_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_toSeqRight_127_);
lean_inc(v_toSeqLeft_126_);
lean_inc(v_toSeq_125_);
lean_inc(v_toFunctor_124_);
lean_dec(v_toApplicative_120_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_181_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___f_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_140_; 
v___f_131_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__1));
v___f_132_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__2));
lean_inc_ref(v_toFunctor_124_);
v___f_133_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_133_, 0, v_toFunctor_124_);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_134_, 0, v_toFunctor_124_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___f_133_);
lean_ctor_set(v___x_135_, 1, v___f_134_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeqRight_127_);
v___f_137_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_137_, 0, v_toSeqLeft_126_);
v___f_138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_138_, 0, v_toSeq_125_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___f_136_);
lean_ctor_set(v___x_129_, 3, v___f_137_);
lean_ctor_set(v___x_129_, 2, v___f_138_);
lean_ctor_set(v___x_129_, 1, v___f_131_);
lean_ctor_set(v___x_129_, 0, v___x_135_);
v___x_140_ = v___x_129_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___f_131_);
lean_ctor_set(v_reuseFailAlloc_180_, 2, v___f_138_);
lean_ctor_set(v_reuseFailAlloc_180_, 3, v___f_137_);
lean_ctor_set(v_reuseFailAlloc_180_, 4, v___f_136_);
v___x_140_ = v_reuseFailAlloc_180_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___f_132_);
lean_ctor_set(v___x_122_, 0, v___x_140_);
v___x_142_ = v___x_122_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___f_132_);
v___x_142_ = v_reuseFailAlloc_179_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v_toApplicative_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_177_; 
v___x_143_ = l_StateRefT_x27_instMonad___redArg(v___x_142_);
v_toApplicative_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v___x_143_, 1);
lean_dec(v_unused_178_);
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_177_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_toApplicative_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_177_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_toFunctor_148_; lean_object* v_toSeq_149_; lean_object* v_toSeqLeft_150_; lean_object* v_toSeqRight_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_175_; 
v_toFunctor_148_ = lean_ctor_get(v_toApplicative_144_, 0);
v_toSeq_149_ = lean_ctor_get(v_toApplicative_144_, 2);
v_toSeqLeft_150_ = lean_ctor_get(v_toApplicative_144_, 3);
v_toSeqRight_151_ = lean_ctor_get(v_toApplicative_144_, 4);
v_isSharedCheck_175_ = !lean_is_exclusive(v_toApplicative_144_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v_toApplicative_144_, 1);
lean_dec(v_unused_176_);
v___x_153_ = v_toApplicative_144_;
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_toSeqRight_151_);
lean_inc(v_toSeqLeft_150_);
lean_inc(v_toSeq_149_);
lean_inc(v_toFunctor_148_);
lean_dec(v_toApplicative_144_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___x_164_; 
v___f_155_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__3));
v___f_156_ = ((lean_object*)(l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___closed__4));
lean_inc_ref(v_toFunctor_148_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_157_, 0, v_toFunctor_148_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_158_, 0, v_toFunctor_148_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___f_157_);
lean_ctor_set(v___x_159_, 1, v___f_158_);
v___f_160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_160_, 0, v_toSeqRight_151_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeqLeft_150_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeq_149_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 4, v___f_160_);
lean_ctor_set(v___x_153_, 3, v___f_161_);
lean_ctor_set(v___x_153_, 2, v___f_162_);
lean_ctor_set(v___x_153_, 1, v___f_155_);
lean_ctor_set(v___x_153_, 0, v___x_159_);
v___x_164_ = v___x_153_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___f_155_);
lean_ctor_set(v_reuseFailAlloc_174_, 2, v___f_162_);
lean_ctor_set(v_reuseFailAlloc_174_, 3, v___f_161_);
lean_ctor_set(v_reuseFailAlloc_174_, 4, v___f_160_);
v___x_164_ = v_reuseFailAlloc_174_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___f_156_);
lean_ctor_set(v___x_146_, 0, v___x_164_);
v___x_166_ = v___x_146_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v___f_156_);
v___x_166_ = v_reuseFailAlloc_173_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_37656__overap_171_; lean_object* v___x_172_; 
v___x_167_ = l_StateRefT_x27_instMonad___redArg(v___x_166_);
v___x_168_ = l_ReaderT_instMonad___redArg(v___x_167_);
v___x_169_ = lean_box(0);
v___x_170_ = l_instInhabitedOfMonad___redArg(v___x_168_, v___x_169_);
v___x_37656__overap_171_ = lean_panic_fn_borrowed(v___x_170_, v_msg_110_);
lean_dec(v___x_170_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
v___x_172_ = lean_apply_7(v___x_37656__overap_171_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, lean_box(0));
return v___x_172_;
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
LEAN_EXPORT void l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_110_ = stack[0].m_obj;
lean_object* v___y_111_ = stack[1].m_obj;
lean_object* v___y_112_ = stack[2].m_obj;
lean_object* v___y_113_ = stack[3].m_obj;
lean_object* v___y_114_ = stack[4].m_obj;
lean_object* v___y_115_ = stack[5].m_obj;
lean_object* v___y_116_ = stack[6].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(v_msg_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1___boxed(lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(v_msg_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_194_;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_198_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__2));
v___x_199_ = lean_unsigned_to_nat(33u);
v___x_200_ = lean_unsigned_to_nat(114u);
v___x_201_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__1));
v___x_202_ = ((lean_object*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__0));
v___x_203_ = l_mkPanicMessageWithDecl(v___x_202_, v___x_201_, v___x_200_, v___x_199_, v___x_198_);
return v___x_203_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(lean_object* v_x_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v_a_213_; 
v___x_212_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_205_);
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v___x_212_);
if (lean_obj_tag(v_a_213_) == 10)
{
lean_object* v_subExpr_214_; lean_object* v_expr_215_; lean_object* v_optionsPerPos_216_; lean_object* v_currNamespace_217_; lean_object* v_openDecls_218_; uint8_t v_inPattern_219_; lean_object* v_depth_220_; lean_object* v_lctxInitIndices_221_; lean_object* v_pos_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_subExpr_214_ = lean_ctor_get(v___y_205_, 3);
v_expr_215_ = lean_ctor_get(v_a_213_, 1);
lean_inc_ref(v_expr_215_);
lean_dec_ref_known(v_a_213_, 2);
v_optionsPerPos_216_ = lean_ctor_get(v___y_205_, 0);
v_currNamespace_217_ = lean_ctor_get(v___y_205_, 1);
v_openDecls_218_ = lean_ctor_get(v___y_205_, 2);
v_inPattern_219_ = lean_ctor_get_uint8(v___y_205_, sizeof(void*)*6);
v_depth_220_ = lean_ctor_get(v___y_205_, 4);
v_lctxInitIndices_221_ = lean_ctor_get(v___y_205_, 5);
v_pos_222_ = lean_ctor_get(v_subExpr_214_, 1);
lean_inc(v_pos_222_);
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_expr_215_);
lean_ctor_set(v___x_223_, 1, v_pos_222_);
lean_inc(v_lctxInitIndices_221_);
lean_inc(v_depth_220_);
lean_inc(v_openDecls_218_);
lean_inc(v_currNamespace_217_);
lean_inc(v_optionsPerPos_216_);
v___x_224_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_224_, 0, v_optionsPerPos_216_);
lean_ctor_set(v___x_224_, 1, v_currNamespace_217_);
lean_ctor_set(v___x_224_, 2, v_openDecls_218_);
lean_ctor_set(v___x_224_, 3, v___x_223_);
lean_ctor_set(v___x_224_, 4, v_depth_220_);
lean_ctor_set(v___x_224_, 5, v_lctxInitIndices_221_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*6, v_inPattern_219_);
lean_inc(v___y_210_);
lean_inc_ref(v___y_209_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
v___x_225_ = lean_apply_7(v_x_204_, v___x_224_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, lean_box(0));
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec(v_a_213_);
lean_dec_ref(v_x_204_);
v___x_226_ = lean_obj_once(&l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3, &l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3_once, _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___closed__3);
v___x_227_ = l_panic___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_spec__1(v___x_226_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
return v___x_227_;
}
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_204_ = stack[0].m_obj;
lean_object* v___y_205_ = stack[1].m_obj;
lean_object* v___y_206_ = stack[2].m_obj;
lean_object* v___y_207_ = stack[3].m_obj;
lean_object* v___y_208_ = stack[4].m_obj;
lean_object* v___y_209_ = stack[5].m_obj;
lean_object* v___y_210_ = stack[6].m_obj;
lean_object* v_res_228_;
v_res_228_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(v_x_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1___boxed(lean_object* v_x_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(v_x_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_237_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__20));
v___x_281_ = l_String_toRawSubstring_x27(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47(void){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Array_mkArray0___redArg();
return v___x_338_;
}
}
lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(lean_object* v_x_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__3));
lean_inc(v_x_343_);
v___x_347_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__8));
lean_inc(v_x_343_);
v___x_349_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__10));
lean_inc(v_x_343_);
v___x_351_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_352_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__11));
v___x_353_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__12));
lean_inc(v_x_343_);
v___x_354_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__14));
lean_inc(v_x_343_);
v___x_356_ = l_Lean_Syntax_isOfKind(v_x_343_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_x_343_);
return v___x_357_;
}
else
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = l_Lean_Syntax_getArg(v_x_343_, v___x_358_);
v___x_360_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16));
lean_inc(v___x_359_);
v___x_361_ = l_Lean_Syntax_isOfKind(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec(v___x_359_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v_x_343_);
return v___x_362_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_363_ = lean_unsigned_to_nat(1u);
v___x_364_ = l_Lean_Syntax_getArg(v___x_359_, v___x_363_);
lean_dec(v___x_359_);
v___x_365_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18));
lean_inc(v___x_364_);
v___x_366_ = l_Lean_Syntax_isOfKind(v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v___x_364_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_x_343_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_368_ = l_Lean_Syntax_getArg(v___x_364_, v___x_358_);
lean_dec(v___x_364_);
v___x_369_ = lean_box(0);
v___x_370_ = l_Lean_Syntax_matchesIdent(v___x_368_, v___x_369_);
lean_dec(v___x_368_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v_x_343_);
return v___x_371_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = lean_unsigned_to_nat(3u);
v___x_373_ = l_Lean_Syntax_getArg(v_x_343_, v___x_372_);
lean_inc(v___x_373_);
v___x_374_ = l_Lean_Syntax_matchesNull(v___x_373_, v___x_363_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
lean_dec(v___x_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_x_343_);
return v___x_375_;
}
else
{
lean_object* v_P_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_P_376_ = l_Lean_Syntax_getArg(v_x_343_, v___x_363_);
lean_dec(v_x_343_);
v___x_377_ = l_Lean_Syntax_getArg(v___x_373_, v___x_358_);
lean_dec(v___x_373_);
v___x_378_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_P_376_, v___y_344_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_toCold_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_406_; 
v_toCold_379_ = lean_ctor_get(v___y_344_, 0);
v_a_380_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_406_ == 0)
{
v___x_382_ = v___x_378_;
v_isShared_383_ = v_isSharedCheck_406_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_378_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_406_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_ref_384_; lean_object* v_quotContext_385_; lean_object* v_currMacroScope_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_ref_384_ = lean_ctor_get(v___y_344_, 2);
v_quotContext_385_ = lean_ctor_get(v_toCold_379_, 8);
v_currMacroScope_386_ = lean_ctor_get(v_toCold_379_, 9);
v___x_387_ = l_Lean_SourceInfo_fromRef(v_ref_384_, v___x_354_);
v___x_388_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19));
lean_inc_n(v___x_387_, 7);
v___x_389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21);
lean_inc(v_currMacroScope_386_);
lean_inc(v_quotContext_385_);
v___x_391_ = l_Lean_addMacroScope(v_quotContext_385_, v___x_369_, v_currMacroScope_386_);
v___x_392_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40));
v___x_393_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_393_, 0, v___x_387_);
lean_ctor_set(v___x_393_, 1, v___x_390_);
lean_ctor_set(v___x_393_, 2, v___x_391_);
lean_ctor_set(v___x_393_, 3, v___x_392_);
v___x_394_ = l_Lean_Syntax_node1(v___x_387_, v___x_365_, v___x_393_);
v___x_395_ = l_Lean_Syntax_node2(v___x_387_, v___x_360_, v___x_389_, v___x_394_);
v___x_396_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41));
v___x_397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_387_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43));
v___x_399_ = l_Lean_Syntax_node1(v___x_387_, v___x_398_, v___x_377_);
v___x_400_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44));
v___x_401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_387_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_Syntax_node5(v___x_387_, v___x_355_, v___x_395_, v_a_380_, v___x_397_, v___x_399_, v___x_401_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_402_);
v___x_404_ = v___x_382_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_dec(v___x_377_);
return v___x_378_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = l_Lean_Syntax_getArg(v_x_343_, v___x_407_);
v___x_409_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__46));
lean_inc(v___x_408_);
v___x_410_ = l_Lean_Syntax_isOfKind(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v___x_408_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v_x_343_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = l_Lean_Syntax_getArg(v___x_408_, v___x_407_);
v___x_414_ = l_Lean_Syntax_matchesNull(v___x_413_, v___x_412_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v___x_408_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v_x_343_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_b_418_; lean_object* v_xs_419_; lean_object* v___x_420_; 
lean_dec(v_x_343_);
v___x_416_ = l_Lean_Syntax_getArg(v___x_408_, v___x_412_);
v___x_417_ = lean_unsigned_to_nat(3u);
v_b_418_ = l_Lean_Syntax_getArg(v___x_408_, v___x_417_);
lean_dec(v___x_408_);
v_xs_419_ = l_Lean_Syntax_getArgs(v___x_416_);
lean_dec(v___x_416_);
v___x_420_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_b_418_, v___y_344_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_440_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_440_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_440_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_440_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_ref_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v_ref_425_ = lean_ctor_get(v___y_344_, 2);
v___x_426_ = l_Lean_SourceInfo_fromRef(v_ref_425_, v___x_351_);
lean_inc_n(v___x_426_, 5);
v___x_427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_352_);
v___x_428_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43));
v___x_429_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47);
v___x_430_ = l_Array_append___redArg(v___x_429_, v_xs_419_);
lean_dec_ref(v_xs_419_);
v___x_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_431_, 0, v___x_426_);
lean_ctor_set(v___x_431_, 1, v___x_428_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
v___x_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_432_, 0, v___x_426_);
lean_ctor_set(v___x_432_, 1, v___x_428_);
lean_ctor_set(v___x_432_, 2, v___x_429_);
v___x_433_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__48));
v___x_434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_426_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_Syntax_node4(v___x_426_, v___x_409_, v___x_431_, v___x_432_, v___x_434_, v_a_421_);
v___x_436_ = l_Lean_Syntax_node2(v___x_426_, v___x_353_, v___x_427_, v___x_435_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_436_);
v___x_438_ = v___x_423_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_dec_ref(v_xs_419_);
return v___x_420_;
}
}
}
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_t_444_; lean_object* v___x_445_; lean_object* v_e_446_; lean_object* v___x_447_; 
v___x_441_ = lean_unsigned_to_nat(1u);
v___x_442_ = l_Lean_Syntax_getArg(v_x_343_, v___x_441_);
v___x_443_ = lean_unsigned_to_nat(3u);
v_t_444_ = l_Lean_Syntax_getArg(v_x_343_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(5u);
v_e_446_ = l_Lean_Syntax_getArg(v_x_343_, v___x_445_);
lean_dec(v_x_343_);
v___x_447_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_t_444_, v___y_344_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_e_446_, v___y_344_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_466_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_466_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_466_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_466_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_ref_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v_ref_454_ = lean_ctor_get(v___y_344_, 2);
v___x_455_ = l_Lean_SourceInfo_fromRef(v_ref_454_, v___x_349_);
v___x_456_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__49));
lean_inc_n(v___x_455_, 3);
v___x_457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__50));
v___x_459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_455_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__51));
v___x_461_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_455_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
v___x_462_ = l_Lean_Syntax_node6(v___x_455_, v___x_350_, v___x_457_, v___x_442_, v___x_459_, v_a_448_, v___x_461_, v_a_450_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_462_);
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_dec(v_a_448_);
lean_dec(v___x_442_);
return v___x_449_;
}
}
else
{
lean_dec(v_e_446_);
lean_dec(v___x_442_);
return v___x_447_;
}
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = l_Lean_Syntax_getArg(v_x_343_, v___x_467_);
v___x_469_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__16));
lean_inc(v___x_468_);
v___x_470_ = l_Lean_Syntax_isOfKind(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_dec(v___x_468_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_x_343_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = l_Lean_Syntax_getArg(v___x_468_, v___x_472_);
lean_dec(v___x_468_);
v___x_474_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__18));
lean_inc(v___x_473_);
v___x_475_ = l_Lean_Syntax_isOfKind(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec(v___x_473_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v_x_343_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_477_ = l_Lean_Syntax_getArg(v___x_473_, v___x_467_);
lean_dec(v___x_473_);
v___x_478_ = lean_box(0);
v___x_479_ = l_Lean_Syntax_matchesIdent(v___x_477_, v___x_478_);
lean_dec(v___x_477_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v_x_343_);
return v___x_480_;
}
else
{
lean_object* v_P_481_; lean_object* v___x_482_; 
v_P_481_ = l_Lean_Syntax_getArg(v_x_343_, v___x_472_);
lean_dec(v_x_343_);
v___x_482_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_P_481_, v___y_344_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_toCold_483_; lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_506_; 
v_toCold_483_ = lean_ctor_get(v___y_344_, 0);
v_a_484_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_506_ == 0)
{
v___x_486_ = v___x_482_;
v_isShared_487_ = v_isSharedCheck_506_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_506_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v_ref_488_; lean_object* v_quotContext_489_; lean_object* v_currMacroScope_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v_ref_488_ = lean_ctor_get(v___y_344_, 2);
v_quotContext_489_ = lean_ctor_get(v_toCold_483_, 8);
v_currMacroScope_490_ = lean_ctor_get(v_toCold_483_, 9);
v___x_491_ = l_Lean_SourceInfo_fromRef(v_ref_488_, v___x_347_);
v___x_492_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__19));
lean_inc_n(v___x_491_, 5);
v___x_493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__21);
lean_inc(v_currMacroScope_490_);
lean_inc(v_quotContext_489_);
v___x_495_ = l_Lean_addMacroScope(v_quotContext_489_, v___x_478_, v_currMacroScope_490_);
v___x_496_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__40));
v___x_497_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_497_, 0, v___x_491_);
lean_ctor_set(v___x_497_, 1, v___x_494_);
lean_ctor_set(v___x_497_, 2, v___x_495_);
lean_ctor_set(v___x_497_, 3, v___x_496_);
v___x_498_ = l_Lean_Syntax_node1(v___x_491_, v___x_474_, v___x_497_);
v___x_499_ = l_Lean_Syntax_node2(v___x_491_, v___x_469_, v___x_493_, v___x_498_);
v___x_500_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__44));
v___x_501_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_491_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_Syntax_node3(v___x_491_, v___x_348_, v___x_499_, v_a_484_, v___x_501_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_502_);
v___x_504_ = v___x_486_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
else
{
return v___x_482_;
}
}
}
}
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = l_Lean_Syntax_getArg(v_x_343_, v___x_507_);
lean_dec(v_x_343_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
}
LEAN_EXPORT void l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_343_ = stack[0].m_obj;
lean_object* v___y_344_ = stack[1].m_obj;
lean_object* v_res_510_;
v_res_510_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_x_343_, v___y_344_);
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___boxed(lean_object* v_x_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_x_511_, v___y_512_);
lean_dec_ref(v___y_512_);
return v_res_514_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(lean_object* v_x_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_a_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_523_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v___y_516_);
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v___x_523_);
v___x_525_ = l_Lean_Expr_appFn_x21(v_a_524_);
lean_dec(v_a_524_);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v___x_525_, v___x_526_, v_x_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v___x_527_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_515_ = stack[0].m_obj;
lean_object* v___y_516_ = stack[1].m_obj;
lean_object* v___y_517_ = stack[2].m_obj;
lean_object* v___y_518_ = stack[3].m_obj;
lean_object* v___y_519_ = stack[4].m_obj;
lean_object* v___y_520_ = stack[5].m_obj;
lean_object* v___y_521_ = stack[6].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v_x_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg___boxed(lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v_x_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(lean_object* v_t_538_, lean_object* v_k_539_, lean_object* v_fallback_540_){
_start:
{
if (lean_obj_tag(v_t_538_) == 0)
{
lean_object* v_k_541_; lean_object* v_v_542_; lean_object* v_l_543_; lean_object* v_r_544_; uint8_t v___x_545_; 
v_k_541_ = lean_ctor_get(v_t_538_, 1);
v_v_542_ = lean_ctor_get(v_t_538_, 2);
v_l_543_ = lean_ctor_get(v_t_538_, 3);
v_r_544_ = lean_ctor_get(v_t_538_, 4);
v___x_545_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_539_, v_k_541_);
switch(v___x_545_)
{
case 0:
{
v_t_538_ = v_l_543_;
goto _start;
}
case 1:
{
lean_inc(v_v_542_);
return v_v_542_;
}
default: 
{
v_t_538_ = v_r_544_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_540_);
return v_fallback_540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg___boxed(lean_object* v_t_548_, lean_object* v_k_549_, lean_object* v_fallback_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_t_548_, v_k_549_, v_fallback_550_);
lean_dec(v_fallback_550_);
lean_dec(v_k_549_);
lean_dec(v_t_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed(lean_object* v_acc_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(v_acc_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_569_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(lean_object* v_acc_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v_a_571_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_680_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_680_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_680_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_680_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; 
lean_inc(v_a_579_);
v___x_583_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_a_579_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v___x_585_; 
lean_dec_ref_known(v___x_583_, 1);
lean_dec(v_a_579_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v_acc_570_);
v___x_585_ = v___x_581_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_acc_570_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v___x_587_; 
lean_dec(v___x_583_);
lean_inc(v_a_579_);
v___x_587_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_a_579_);
if (lean_obj_tag(v___x_587_) == 1)
{
lean_object* v_snd_588_; lean_object* v_val_589_; lean_object* v_fst_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_670_; 
lean_dec(v_a_579_);
v_snd_588_ = lean_ctor_get(v_acc_570_, 1);
lean_inc(v_snd_588_);
v_val_589_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_val_589_);
lean_dec_ref_known(v___x_587_, 1);
v_fst_590_ = lean_ctor_get(v_acc_570_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v_acc_570_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_acc_570_, 1);
lean_dec(v_unused_671_);
v___x_592_ = v_acc_570_;
v_isShared_593_ = v_isSharedCheck_670_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_fst_590_);
lean_dec(v_acc_570_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_670_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_669_; 
v_fst_594_ = lean_ctor_get(v_snd_588_, 0);
v_snd_595_ = lean_ctor_get(v_snd_588_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_snd_588_);
if (v_isSharedCheck_669_ == 0)
{
v___x_597_ = v_snd_588_;
v_isShared_598_ = v_isSharedCheck_669_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snd_595_);
lean_inc(v_fst_594_);
lean_dec(v_snd_588_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_669_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___y_600_; lean_object* v_accessibles_601_; lean_object* v_inaccessibles_602_; lean_object* v_name_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v_val_655_; 
v_name_613_ = lean_ctor_get(v_val_589_, 0);
lean_inc(v_name_613_);
lean_dec(v_val_589_);
v___x_614_ = l_Lean_Name_eraseMacroScopes(v_name_613_);
v___x_615_ = l_Lean_Name_hasMacroScopes(v_name_613_);
lean_dec(v_name_613_);
if (v___x_615_ == 0)
{
lean_object* v___x_664_; 
v___x_664_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_fst_590_, v___x_614_);
if (lean_obj_tag(v___x_664_) == 1)
{
lean_object* v_val_665_; 
v_val_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v___x_664_, 1);
v_val_655_ = v_val_665_;
goto v___jp_654_;
}
else
{
lean_object* v___x_666_; 
lean_dec(v___x_664_);
v___x_666_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_614_);
v_fst_617_ = v___x_666_;
v_snd_618_ = v___x_614_;
goto v___jp_616_;
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_fst_594_, v___x_614_, v___x_667_);
v_val_655_ = v___x_668_;
goto v___jp_654_;
}
v___jp_599_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = lean_array_push(v_snd_595_, v___y_600_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v___x_603_);
lean_ctor_set(v___x_597_, 0, v_inaccessibles_602_);
v___x_605_ = v___x_597_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_inaccessibles_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_603_);
v___x_605_ = v_reuseFailAlloc_612_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_605_);
lean_ctor_set(v___x_592_, 0, v_accessibles_601_);
v___x_607_ = v___x_592_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_accessibles_601_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_607_);
v___x_609_ = v___x_581_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
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
v___jp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = l_Lean_mkIdent(v_snd_618_);
v___x_620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0));
v___x_621_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__1(v___x_620_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_622_, v_a_575_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v_ref_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v_ref_625_ = lean_ctor_get(v_a_575_, 2);
v___x_626_ = 0;
v___x_627_ = l_Lean_SourceInfo_fromRef(v_ref_625_, v___x_626_);
v___x_628_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__3));
v___x_629_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__41));
lean_inc(v___x_627_);
v___x_630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_627_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_Syntax_node3(v___x_627_, v___x_628_, v___x_619_, v___x_630_, v_a_624_);
if (v___x_615_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_614_, v_fst_617_, v_fst_590_);
v___y_600_ = v___x_631_;
v_accessibles_601_ = v___x_632_;
v_inaccessibles_602_ = v_fst_594_;
goto v___jp_599_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_614_, v_fst_617_, v_fst_594_);
v___y_600_ = v___x_631_;
v_accessibles_601_ = v_fst_590_;
v_inaccessibles_602_ = v___x_633_;
goto v___jp_599_;
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v___x_619_);
lean_dec(v_fst_617_);
lean_dec(v___x_614_);
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_del_object(v___x_592_);
lean_dec(v_fst_590_);
lean_del_object(v___x_581_);
v_a_634_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_623_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_623_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v___x_619_);
lean_dec(v_fst_617_);
lean_dec(v___x_614_);
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_del_object(v___x_592_);
lean_dec(v_fst_590_);
lean_del_object(v___x_581_);
v_a_642_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_621_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_621_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
v___jp_650_:
{
lean_object* v___x_653_; 
lean_inc(v___x_614_);
v___x_653_ = lean_name_append_after(v___x_614_, v___y_652_);
v_fst_617_ = v___y_651_;
v_snd_618_ = v___x_653_;
goto v___jp_616_;
}
v___jp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_val_655_, v___x_656_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_nat_dec_eq(v_val_655_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4));
v___x_661_ = l_Nat_toSuperscriptString(v_val_655_);
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
lean_dec_ref(v___x_661_);
v___y_651_ = v___x_657_;
v___y_652_ = v___x_662_;
goto v___jp_650_;
}
else
{
lean_object* v___x_663_; 
lean_dec(v_val_655_);
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__4));
v___y_651_ = v___x_657_;
v___y_652_ = v___x_663_;
goto v___jp_650_;
}
}
}
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v___x_587_);
lean_del_object(v___x_581_);
v___x_672_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_a_579_);
lean_dec(v_a_579_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v_acc_570_);
v___x_673_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
return v___x_673_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed), 8, 1);
lean_closure_set(v___x_674_, 0, v_acc_570_);
v___x_675_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_674_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___boxed), 8, 1);
lean_closure_set(v___x_677_, 0, v_a_676_);
v___x_678_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___boxed), 9, 2);
lean_closure_set(v___x_678_, 0, lean_box(0));
lean_closure_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v___x_678_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
return v___x_679_;
}
else
{
return v___x_675_;
}
}
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_acc_570_);
v_a_681_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_578_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_578_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_570_ = stack[0].m_obj;
lean_object* v_a_571_ = stack[1].m_obj;
lean_object* v_a_572_ = stack[2].m_obj;
lean_object* v_a_573_ = stack[3].m_obj;
lean_object* v_a_574_ = stack[4].m_obj;
lean_object* v_a_575_ = stack[5].m_obj;
lean_object* v_a_576_ = stack[6].m_obj;
lean_object* v_res_689_;
v_res_689_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses(v_acc_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
stack->m_obj
 = v_res_689_;
}
lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(lean_object* v_x_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_x_690_, v___y_695_);
return v___x_698_;
}
}
LEAN_EXPORT void l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_690_ = stack[0].m_obj;
lean_object* v___y_691_ = stack[1].m_obj;
lean_object* v___y_692_ = stack[2].m_obj;
lean_object* v___y_693_ = stack[3].m_obj;
lean_object* v___y_694_ = stack[4].m_obj;
lean_object* v___y_695_ = stack[5].m_obj;
lean_object* v___y_696_ = stack[6].m_obj;
lean_object* v_res_699_;
v_res_699_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(v_x_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___boxed(lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2(v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3(lean_object* v_00_u03b4_709_, lean_object* v_t_710_, lean_object* v_k_711_, lean_object* v_fallback_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___redArg(v_t_710_, v_k_711_, v_fallback_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3___boxed(lean_object* v_00_u03b4_714_, lean_object* v_t_715_, lean_object* v_k_716_, lean_object* v_fallback_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__3(v_00_u03b4_714_, v_t_715_, v_k_716_, v_fallback_717_);
lean_dec(v_fallback_717_);
lean_dec(v_k_716_);
lean_dec(v_t_715_);
return v_res_718_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(lean_object* v_00_u03b1_719_, lean_object* v_child_720_, lean_object* v_childIdx_721_, lean_object* v_x_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___redArg(v_child_720_, v_childIdx_721_, v_x_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_child_720_ = stack[1].m_obj;
lean_object* v_childIdx_721_ = stack[2].m_obj;
lean_object* v_x_722_ = stack[3].m_obj;
lean_object* v___y_723_ = stack[4].m_obj;
lean_object* v___y_724_ = stack[5].m_obj;
lean_object* v___y_725_ = stack[6].m_obj;
lean_object* v___y_726_ = stack[7].m_obj;
lean_object* v___y_727_ = stack[8].m_obj;
lean_object* v___y_728_ = stack[9].m_obj;
lean_object* v_res_731_;
v_res_731_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(lean_box(0), v_child_720_, v_childIdx_721_, v_x_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5___boxed(lean_object* v_00_u03b1_732_, lean_object* v_child_733_, lean_object* v_childIdx_734_, lean_object* v_x_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4_spec__5(v_00_u03b1_732_, v_child_733_, v_childIdx_734_, v_x_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_743_;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(lean_object* v_00_u03b1_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
return v___x_753_;
}
}
LEAN_EXPORT void l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_745_ = stack[1].m_obj;
lean_object* v___y_746_ = stack[2].m_obj;
lean_object* v___y_747_ = stack[3].m_obj;
lean_object* v___y_748_ = stack[4].m_obj;
lean_object* v___y_749_ = stack[5].m_obj;
lean_object* v___y_750_ = stack[6].m_obj;
lean_object* v___y_751_ = stack[7].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(lean_box(0), v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___boxed(lean_object* v_00_u03b1_755_, lean_object* v_x_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5(v_00_u03b1_755_, v_x_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_764_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_836_; lean_object* v_a_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_836_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__0___redArg(v_a_784_);
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref(v___x_836_);
v___x_838_ = lean_unsigned_to_nat(3u);
v___x_839_ = l_Lean_Expr_getAppNumArgs(v_a_837_);
lean_dec(v_a_837_);
v___x_840_ = lean_nat_dec_le(v___x_838_, v___x_839_);
lean_dec(v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_PrettyPrinter_Delaborator_failure___redArg();
if (lean_obj_tag(v___x_841_) == 0)
{
lean_dec_ref_known(v___x_841_, 1);
goto v___jp_791_;
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
goto v___jp_791_;
}
v___jp_791_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__4));
v___x_793_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__5___redArg(v___x_792_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v_snd_795_; lean_object* v_snd_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_826_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v_snd_795_ = lean_ctor_get(v_a_794_, 1);
lean_inc(v_snd_795_);
lean_dec(v_a_794_);
v_snd_796_ = lean_ctor_get(v_snd_795_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_snd_795_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_snd_795_, 0);
lean_dec(v_unused_827_);
v___x_798_ = v_snd_795_;
v_isShared_799_ = v_isSharedCheck_826_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_snd_796_);
lean_dec(v_snd_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_826_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0));
v___x_801_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_800_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
v___x_803_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_802_, v_a_788_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_825_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_825_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_825_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_825_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_ref_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
v_ref_808_ = lean_ctor_get(v_a_788_, 2);
v___x_809_ = 0;
v___x_810_ = l_Lean_SourceInfo_fromRef(v_ref_808_, v___x_809_);
v___x_811_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__6));
v___x_812_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__43));
v___x_813_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47, &l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47_once, _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg___closed__47);
v___x_814_ = l_Array_reverse___redArg(v_snd_796_);
v___x_815_ = l_Array_append___redArg(v___x_813_, v___x_814_);
lean_dec_ref(v___x_814_);
lean_inc_n(v___x_810_, 2);
v___x_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_816_, 0, v___x_810_);
lean_ctor_set(v___x_816_, 1, v___x_812_);
lean_ctor_set(v___x_816_, 2, v___x_815_);
v___x_817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___closed__7));
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 2);
lean_ctor_set(v___x_798_, 1, v___x_817_);
lean_ctor_set(v___x_798_, 0, v___x_810_);
v___x_819_ = v___x_798_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_817_);
v___x_819_ = v_reuseFailAlloc_824_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = l_Lean_Syntax_node3(v___x_810_, v___x_811_, v___x_816_, v___x_819_, v_a_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_820_);
v___x_822_ = v___x_806_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_del_object(v___x_798_);
lean_dec(v_snd_796_);
return v___x_803_;
}
}
else
{
lean_del_object(v___x_798_);
lean_dec(v_snd_796_);
return v___x_801_;
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_a_828_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_793_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_793_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_784_ = stack[0].m_obj;
lean_object* v_a_785_ = stack[1].m_obj;
lean_object* v_a_786_ = stack[2].m_obj;
lean_object* v_a_787_ = stack[3].m_obj;
lean_object* v_a_788_ = stack[4].m_obj;
lean_object* v_a_789_ = stack[5].m_obj;
lean_object* v_res_850_;
v_res_850_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
stack->m_obj
 = v_res_850_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___boxed(lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal(v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_858_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1(){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__2));
v___x_917_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___closed__21));
v___x_918_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___boxed), 7, 0);
v___x_919_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_915_, v___x_916_, v___x_917_, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_920_;
v_res_920_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1();
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1___boxed(lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal__1();
return v_res_922_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses___closed__0));
v___x_931_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__4___redArg(v___x_930_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabMGoal_delabHypotheses_spec__2___redArg(v_a_932_, v_a_927_);
return v___x_933_;
}
else
{
return v___x_931_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_923_ = stack[0].m_obj;
lean_object* v_a_924_ = stack[1].m_obj;
lean_object* v_a_925_ = stack[2].m_obj;
lean_object* v_a_926_ = stack[3].m_obj;
lean_object* v_a_927_ = stack[4].m_obj;
lean_object* v_a_928_ = stack[5].m_obj;
lean_object* v_res_934_;
v_res_934_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___boxed(lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker(v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_942_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1(){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_955_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__1));
v___x_957_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___closed__3));
v___x_958_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___boxed), 7, 0);
v___x_959_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_955_, v___x_956_, v___x_957_, v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_960_;
v_res_960_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1();
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1___boxed(lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker___regBuiltin___private_Lean_Elab_Tactic_Do_ProofMode_Delab_0__Lean_Elab_Tactic_Do_ProofMode_delabHypMarker__1();
return v_res_962_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Delab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
