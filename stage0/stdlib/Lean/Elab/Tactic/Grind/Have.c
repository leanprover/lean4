// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Have
// Imports: public import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Tactic.Grind.Intro import Lean.Meta.Tactic.Grind.RevertAll import Lean.Elab.SyntheticMVars import Lean.Meta.Tactic.Grind.Solve
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_setGoals___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getGoals___redArg(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_throwNoGoalsToBeSolved___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Meta_Grind_markGrindName(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 30, 230, 20, 64, 162, 204, 1)}};
static const lean_ctor_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 17, 142, 189, 192, 166, 31, 124)}};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "reuse stopped: guard failed at "};
static const lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_intros___boxed, .m_arity = 14, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "value has metavariables"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "type has metavariables"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "elaborated term is not a `have` declaration"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "have"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4_value),LEAN_SCALAR_PTR_LITERAL(148, 36, 229, 233, 71, 216, 202, 183)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2_value),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Have"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(50, 85, 155, 65, 132, 242, 211, 37)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(51, 204, 138, 180, 88, 218, 18, 142)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 232, 225, 231, 56, 205, 136, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9_value),((lean_object*)&l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(236, 42, 200, 188, 102, 144, 69, 191)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 47, 51, 75, 167, 222, 59, 62)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 248, 130, 10, 202, 243, 86, 79)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "evalHave"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(25, 248, 247, 136, 248, 87, 133, 48)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "`finish` failed\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "this"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(38, 116, 214, 236, 212, 160, 188, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "haveSilent"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 40, 33, 99, 54, 221, 176, 65)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalHaveSilent"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 35, 55, 25, 171, 128, 130, 141)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v_e_30_, v___y_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(lean_object* v_stx_52_, lean_object* v_expectedType_x3f_53_, uint8_t v_mayPostpone_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
uint8_t v___x_64_; lean_object* v___x_65_; 
v___x_64_ = 1;
lean_inc(v_a_62_);
lean_inc_ref(v_a_61_);
lean_inc(v_a_60_);
lean_inc_ref(v_a_59_);
lean_inc(v_a_58_);
lean_inc_ref(v_a_57_);
v___x_65_ = l_Lean_Elab_Term_elabTerm(v_stx_52_, v_expectedType_x3f_53_, v___x_64_, v___x_64_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; uint8_t v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_65_);
v___x_67_ = l_Lean_Elab_Term_PostponeBehavior_ofBool(v_mayPostpone_54_);
v___x_68_ = 0;
lean_inc(v_a_60_);
v___x_69_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_67_, v___x_68_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v___x_69_);
v___x_70_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v_a_66_, v_a_60_);
lean_dec(v_a_60_);
return v___x_70_;
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
lean_dec(v_a_66_);
lean_dec(v_a_60_);
v_a_71_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_69_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
else
{
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed(lean_object* v_stx_79_, lean_object* v_expectedType_x3f_80_, lean_object* v_mayPostpone_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
uint8_t v_mayPostpone_boxed_91_; lean_object* v_res_92_; 
v_mayPostpone_boxed_91_ = lean_unbox(v_mayPostpone_81_);
v_res_92_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(v_stx_79_, v_expectedType_x3f_80_, v_mayPostpone_boxed_91_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(lean_object* v_a_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_apply_2(v_a_93_, v___y_94_, v___y_95_);
v___x_104_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___x_103_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg___boxed(lean_object* v_a_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(v_a_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(lean_object* v_00_u03b1_116_, lean_object* v_a_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(v_a_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___boxed(lean_object* v_00_u03b1_128_, lean_object* v_a_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(v_00_u03b1_128_, v_a_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(uint8_t v_cond_140_, lean_object* v_____r_141_){
_start:
{
if (v_cond_140_ == 0)
{
uint8_t v___x_142_; 
v___x_142_ = 1;
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed(lean_object* v_cond_144_, lean_object* v_____r_145_){
_start:
{
uint8_t v_cond_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_cond_boxed_146_ = lean_unbox(v_cond_144_);
v_res_147_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_boxed_146_, v_____r_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(lean_object* v___f_149_, lean_object* v_x_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_apply_1(v___f_149_, v___x_151_);
v___x_153_ = lean_unbox(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed(lean_object* v___f_154_, lean_object* v_x_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(v___f_154_, v_x_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(uint8_t v_cond_166_, lean_object* v_act_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_options_177_; lean_object* v_declName_x3f_178_; lean_object* v_macroStack_179_; uint8_t v_mayPostpone_180_; uint8_t v_errToSorry_181_; lean_object* v_autoBoundImplicitContext_182_; lean_object* v_autoBoundImplicitForbidden_183_; lean_object* v_sectionVars_184_; lean_object* v_sectionFVars_185_; uint8_t v_implicitLambda_186_; uint8_t v_heedElabAsElim_187_; uint8_t v_isNoncomputableSection_188_; uint8_t v_ignoreTCFailures_189_; uint8_t v_inPattern_190_; lean_object* v_tacSnap_x3f_191_; uint8_t v_saveRecAppSyntax_192_; uint8_t v_holesAsSyntheticOpaque_193_; uint8_t v_checkDeprecated_194_; lean_object* v_fixedTermElabs_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_235_; 
v_options_177_ = lean_ctor_get(v___y_174_, 2);
v_declName_x3f_178_ = lean_ctor_get(v___y_170_, 0);
v_macroStack_179_ = lean_ctor_get(v___y_170_, 1);
v_mayPostpone_180_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8);
v_errToSorry_181_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_182_ = lean_ctor_get(v___y_170_, 2);
v_autoBoundImplicitForbidden_183_ = lean_ctor_get(v___y_170_, 3);
v_sectionVars_184_ = lean_ctor_get(v___y_170_, 4);
v_sectionFVars_185_ = lean_ctor_get(v___y_170_, 5);
v_implicitLambda_186_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 2);
v_heedElabAsElim_187_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_188_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 4);
v_ignoreTCFailures_189_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 5);
v_inPattern_190_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 6);
v_tacSnap_x3f_191_ = lean_ctor_get(v___y_170_, 6);
v_saveRecAppSyntax_192_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 7);
v_holesAsSyntheticOpaque_193_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 8);
v_checkDeprecated_194_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 9);
v_fixedTermElabs_195_ = lean_ctor_get(v___y_170_, 7);
v_isSharedCheck_235_ = !lean_is_exclusive(v___y_170_);
if (v_isSharedCheck_235_ == 0)
{
v___x_197_ = v___y_170_;
v_isShared_198_ = v_isSharedCheck_235_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_fixedTermElabs_195_);
lean_inc(v_tacSnap_x3f_191_);
lean_inc(v_sectionFVars_185_);
lean_inc(v_sectionVars_184_);
lean_inc(v_autoBoundImplicitForbidden_183_);
lean_inc(v_autoBoundImplicitContext_182_);
lean_inc(v_macroStack_179_);
lean_inc(v_declName_x3f_178_);
lean_dec(v___y_170_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_235_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___y_200_; uint8_t v___y_206_; 
if (lean_obj_tag(v_tacSnap_x3f_191_) == 0)
{
v___y_200_ = v_tacSnap_x3f_191_;
goto v___jp_199_;
}
else
{
lean_object* v_val_208_; lean_object* v_old_x3f_209_; lean_object* v___x_210_; lean_object* v___f_211_; 
v_val_208_ = lean_ctor_get(v_tacSnap_x3f_191_, 0);
v_old_x3f_209_ = lean_ctor_get(v_val_208_, 0);
v___x_210_ = lean_box(v_cond_166_);
v___f_211_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_211_, 0, v___x_210_);
if (lean_obj_tag(v_old_x3f_209_) == 1)
{
if (v_cond_166_ == 0)
{
lean_dec_ref(v___f_211_);
goto v___jp_212_;
}
else
{
lean_object* v_val_215_; lean_object* v_map_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_val_215_ = lean_ctor_get(v_old_x3f_209_, 0);
v_map_216_ = lean_ctor_get(v_options_177_, 0);
v___x_217_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3));
v___x_218_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_216_, v___x_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_dec_ref(v___f_211_);
goto v___jp_212_;
}
else
{
lean_object* v_val_219_; 
v_val_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_219_);
lean_dec_ref(v___x_218_);
if (lean_obj_tag(v_val_219_) == 1)
{
uint8_t v_v_220_; 
v_v_220_ = lean_ctor_get_uint8(v_val_219_, 0);
lean_dec_ref(v_val_219_);
if (v_v_220_ == 0)
{
lean_dec_ref(v___f_211_);
goto v___jp_212_;
}
else
{
lean_object* v_stx_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_stx_221_ = lean_ctor_get(v_val_215_, 0);
v___f_222_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_222_, 0, v___f_211_);
v___x_223_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4));
v___x_224_ = lean_box(0);
v___x_225_ = 0;
lean_inc(v_stx_221_);
v___x_226_ = l_Lean_Syntax_formatStx(v_stx_221_, v___x_224_, v___x_225_);
v___x_227_ = l_Std_Format_defWidth;
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Std_Format_pretty(v___x_226_, v___x_227_, v___x_228_, v___x_228_);
v___x_230_ = lean_string_append(v___x_223_, v___x_229_);
lean_dec_ref(v___x_229_);
v___x_231_ = lean_dbg_trace(v___x_230_, v___f_222_);
v___x_232_ = lean_unbox(v___x_231_);
lean_dec(v___x_231_);
v___y_206_ = v___x_232_;
goto v___jp_205_;
}
}
else
{
lean_dec(v_val_219_);
lean_dec_ref(v___f_211_);
goto v___jp_212_;
}
}
}
}
else
{
lean_object* v___x_233_; uint8_t v___x_234_; 
lean_dec_ref(v___f_211_);
v___x_233_ = lean_box(0);
v___x_234_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_166_, v___x_233_);
v___y_206_ = v___x_234_;
goto v___jp_205_;
}
v___jp_212_:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_box(0);
v___x_214_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_166_, v___x_213_);
v___y_206_ = v___x_214_;
goto v___jp_205_;
}
}
v___jp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 6, v___y_200_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 8, 10);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_declName_x3f_178_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_macroStack_179_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_autoBoundImplicitContext_182_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_autoBoundImplicitForbidden_183_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_sectionVars_184_);
lean_ctor_set(v_reuseFailAlloc_204_, 5, v_sectionFVars_185_);
lean_ctor_set(v_reuseFailAlloc_204_, 6, v___y_200_);
lean_ctor_set(v_reuseFailAlloc_204_, 7, v_fixedTermElabs_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8, v_mayPostpone_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 1, v_errToSorry_181_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 2, v_implicitLambda_186_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 3, v_heedElabAsElim_187_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 4, v_isNoncomputableSection_188_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 5, v_ignoreTCFailures_189_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 6, v_inPattern_190_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 7, v_saveRecAppSyntax_192_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 8, v_holesAsSyntheticOpaque_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*8 + 9, v_checkDeprecated_194_);
v___x_202_ = v_reuseFailAlloc_204_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = lean_apply_9(v_act_167_, v___y_168_, v___y_169_, v___x_202_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, lean_box(0));
return v___x_203_;
}
}
v___jp_205_:
{
if (v___y_206_ == 0)
{
lean_object* v___x_207_; 
lean_dec(v_tacSnap_x3f_191_);
v___x_207_ = lean_box(0);
v___y_200_ = v___x_207_;
goto v___jp_199_;
}
else
{
v___y_200_ = v_tacSnap_x3f_191_;
goto v___jp_199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(lean_object* v_cond_236_, lean_object* v_act_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v_cond_boxed_247_; lean_object* v_res_248_; 
v_cond_boxed_247_ = lean_unbox(v_cond_236_);
v_res_248_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v_cond_boxed_247_, v_act_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(lean_object* v_00_u03b1_249_, uint8_t v_cond_250_, lean_object* v_act_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v_cond_250_, v_act_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(lean_object* v_00_u03b1_262_, lean_object* v_cond_263_, lean_object* v_act_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
uint8_t v_cond_boxed_274_; lean_object* v_res_275_; 
v_cond_boxed_274_ = lean_unbox(v_cond_263_);
v_res_275_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(v_00_u03b1_262_, v_cond_boxed_274_, v_act_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(lean_object* v_stx_276_, lean_object* v_expectedType_x3f_277_, uint8_t v_mayPostpone_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_toContext_288_; uint8_t v_recover_289_; 
v_toContext_288_ = lean_ctor_get(v___y_279_, 0);
v_recover_289_ = lean_ctor_get_uint8(v_toContext_288_, sizeof(void*)*1);
if (v_recover_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_box(v_mayPostpone_278_);
v___x_291_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed), 12, 3);
lean_closure_set(v___x_291_, 0, v_stx_276_);
lean_closure_set(v___x_291_, 1, v_expectedType_x3f_277_);
lean_closure_set(v___x_291_, 2, v___x_290_);
v___x_292_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(v___x_291_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
return v___x_292_;
}
else
{
lean_object* v___x_293_; 
v___x_293_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(v_stx_276_, v_expectedType_x3f_277_, v_mayPostpone_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(lean_object* v_stx_294_, lean_object* v_expectedType_x3f_295_, lean_object* v_mayPostpone_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
uint8_t v_mayPostpone_boxed_306_; lean_object* v_res_307_; 
v_mayPostpone_boxed_306_ = lean_unbox(v_mayPostpone_296_);
v_res_307_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(v_stx_294_, v_expectedType_x3f_295_, v_mayPostpone_boxed_306_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(lean_object* v_stx_308_, lean_object* v_expectedType_x3f_309_, uint8_t v_mayPostpone_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_fileName_320_; lean_object* v_fileMap_321_; lean_object* v_options_322_; lean_object* v_currRecDepth_323_; lean_object* v_maxRecDepth_324_; lean_object* v_ref_325_; lean_object* v_currNamespace_326_; lean_object* v_openDecls_327_; lean_object* v_initHeartbeats_328_; lean_object* v_maxHeartbeats_329_; lean_object* v_quotContext_330_; lean_object* v_currMacroScope_331_; uint8_t v_diag_332_; lean_object* v_cancelTk_x3f_333_; uint8_t v_suppressElabErrors_334_; lean_object* v_inheritedTraceOptions_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_348_; 
v_fileName_320_ = lean_ctor_get(v_a_317_, 0);
v_fileMap_321_ = lean_ctor_get(v_a_317_, 1);
v_options_322_ = lean_ctor_get(v_a_317_, 2);
v_currRecDepth_323_ = lean_ctor_get(v_a_317_, 3);
v_maxRecDepth_324_ = lean_ctor_get(v_a_317_, 4);
v_ref_325_ = lean_ctor_get(v_a_317_, 5);
v_currNamespace_326_ = lean_ctor_get(v_a_317_, 6);
v_openDecls_327_ = lean_ctor_get(v_a_317_, 7);
v_initHeartbeats_328_ = lean_ctor_get(v_a_317_, 8);
v_maxHeartbeats_329_ = lean_ctor_get(v_a_317_, 9);
v_quotContext_330_ = lean_ctor_get(v_a_317_, 10);
v_currMacroScope_331_ = lean_ctor_get(v_a_317_, 11);
v_diag_332_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*14);
v_cancelTk_x3f_333_ = lean_ctor_get(v_a_317_, 12);
v_suppressElabErrors_334_ = lean_ctor_get_uint8(v_a_317_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_335_ = lean_ctor_get(v_a_317_, 13);
v_isSharedCheck_348_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_348_ == 0)
{
v___x_337_ = v_a_317_;
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_inheritedTraceOptions_335_);
lean_inc(v_cancelTk_x3f_333_);
lean_inc(v_currMacroScope_331_);
lean_inc(v_quotContext_330_);
lean_inc(v_maxHeartbeats_329_);
lean_inc(v_initHeartbeats_328_);
lean_inc(v_openDecls_327_);
lean_inc(v_currNamespace_326_);
lean_inc(v_ref_325_);
lean_inc(v_maxRecDepth_324_);
lean_inc(v_currRecDepth_323_);
lean_inc(v_options_322_);
lean_inc(v_fileMap_321_);
lean_inc(v_fileName_320_);
lean_dec(v_a_317_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_348_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___f_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v_ref_343_; lean_object* v___x_345_; 
v___x_339_ = lean_box(v_mayPostpone_310_);
lean_inc(v_stx_308_);
v___f_340_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed), 12, 3);
lean_closure_set(v___f_340_, 0, v_stx_308_);
lean_closure_set(v___f_340_, 1, v_expectedType_x3f_309_);
lean_closure_set(v___f_340_, 2, v___x_339_);
v___x_341_ = 1;
v___x_342_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_342_, 0, lean_box(0));
lean_closure_set(v___x_342_, 1, v___f_340_);
v_ref_343_ = l_Lean_replaceRef(v_stx_308_, v_ref_325_);
lean_dec(v_ref_325_);
lean_dec(v_stx_308_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 5, v_ref_343_);
v___x_345_ = v___x_337_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_fileName_320_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_fileMap_321_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v_options_322_);
lean_ctor_set(v_reuseFailAlloc_347_, 3, v_currRecDepth_323_);
lean_ctor_set(v_reuseFailAlloc_347_, 4, v_maxRecDepth_324_);
lean_ctor_set(v_reuseFailAlloc_347_, 5, v_ref_343_);
lean_ctor_set(v_reuseFailAlloc_347_, 6, v_currNamespace_326_);
lean_ctor_set(v_reuseFailAlloc_347_, 7, v_openDecls_327_);
lean_ctor_set(v_reuseFailAlloc_347_, 8, v_initHeartbeats_328_);
lean_ctor_set(v_reuseFailAlloc_347_, 9, v_maxHeartbeats_329_);
lean_ctor_set(v_reuseFailAlloc_347_, 10, v_quotContext_330_);
lean_ctor_set(v_reuseFailAlloc_347_, 11, v_currMacroScope_331_);
lean_ctor_set(v_reuseFailAlloc_347_, 12, v_cancelTk_x3f_333_);
lean_ctor_set(v_reuseFailAlloc_347_, 13, v_inheritedTraceOptions_335_);
lean_ctor_set_uint8(v_reuseFailAlloc_347_, sizeof(void*)*14, v_diag_332_);
lean_ctor_set_uint8(v_reuseFailAlloc_347_, sizeof(void*)*14 + 1, v_suppressElabErrors_334_);
v___x_345_ = v_reuseFailAlloc_347_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v___x_341_, v___x_342_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v___x_345_, v_a_318_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(lean_object* v_stx_349_, lean_object* v_expectedType_x3f_350_, lean_object* v_mayPostpone_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_mayPostpone_boxed_361_; lean_object* v_res_362_; 
v_mayPostpone_boxed_361_ = lean_unbox(v_mayPostpone_351_);
v_res_362_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(v_stx_349_, v_expectedType_x3f_350_, v_mayPostpone_boxed_361_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v_res_362_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
v___x_364_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg(){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___boxed(lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(lean_object* v_00_u03b1_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(lean_object* v_00_u03b1_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(v_00_u03b1_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(lean_object* v_msgData_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_env_400_; lean_object* v___x_401_; lean_object* v_mctx_402_; lean_object* v_lctx_403_; lean_object* v_options_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_399_ = lean_st_ref_get(v___y_397_);
v_env_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc_ref(v_env_400_);
lean_dec(v___x_399_);
v___x_401_ = lean_st_ref_get(v___y_395_);
v_mctx_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_mctx_402_);
lean_dec(v___x_401_);
v_lctx_403_ = lean_ctor_get(v___y_394_, 2);
v_options_404_ = lean_ctor_get(v___y_396_, 2);
lean_inc_ref(v_options_404_);
lean_inc_ref(v_lctx_403_);
v___x_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_405_, 0, v_env_400_);
lean_ctor_set(v___x_405_, 1, v_mctx_402_);
lean_ctor_set(v___x_405_, 2, v_lctx_403_);
lean_ctor_set(v___x_405_, 3, v_options_404_);
v___x_406_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v_msgData_393_);
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1___boxed(lean_object* v_msgData_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(v_msgData_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_ref_421_; lean_object* v___x_422_; lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_431_; 
v_ref_421_ = lean_ctor_get(v___y_418_, 5);
v___x_422_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(v_msg_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_431_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_431_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_429_; 
lean_inc(v_ref_421_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_ref_421_);
lean_ctor_set(v___x_427_, 1, v_a_423_);
if (v_isShared_426_ == 0)
{
lean_ctor_set_tag(v___x_425_, 1);
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___boxed(lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5(void){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Array_mkArray0(lean_box(0));
return v___x_445_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7));
v___x_449_ = l_String_toRawSubstring_x27(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15));
v___x_467_ = l_Lean_stringToMessageData(v___x_466_);
return v___x_467_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17));
v___x_470_ = l_Lean_stringToMessageData(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(uint8_t v___x_474_, lean_object* v_stx_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
if (v___x_474_ == 0)
{
lean_object* v___x_488_; 
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___x_478_);
lean_dec_ref(v___x_477_);
lean_dec_ref(v___x_476_);
v___x_488_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = l_Lean_Syntax_getArg(v_stx_475_, v___x_489_);
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0));
v___x_492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1));
lean_inc_ref(v___x_477_);
lean_inc_ref(v___x_476_);
v___x_493_ = l_Lean_Name_mkStr4(v___x_476_, v___x_477_, v___x_491_, v___x_492_);
lean_inc(v___x_490_);
v___x_494_ = l_Lean_Syntax_isOfKind(v___x_490_, v___x_493_);
lean_dec(v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v___x_490_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v___x_478_);
lean_dec_ref(v___x_477_);
lean_dec_ref(v___x_476_);
v___x_495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_495_;
}
else
{
lean_object* v_ref_496_; lean_object* v_quotContext_497_; lean_object* v_currMacroScope_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v_ref_496_ = lean_ctor_get(v___y_485_, 5);
v_quotContext_497_ = lean_ctor_get(v___y_485_, 10);
v_currMacroScope_498_ = lean_ctor_get(v___y_485_, 11);
v___x_499_ = 0;
v___x_500_ = l_Lean_SourceInfo_fromRef(v_ref_496_, v___x_499_);
lean_inc_ref(v___x_478_);
lean_inc_ref(v___x_477_);
lean_inc_ref(v___x_476_);
v___x_501_ = l_Lean_Name_mkStr4(v___x_476_, v___x_477_, v___x_491_, v___x_478_);
lean_inc(v___x_500_);
v___x_502_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_478_);
v___x_503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2));
v___x_504_ = l_Lean_Name_mkStr4(v___x_476_, v___x_477_, v___x_491_, v___x_503_);
v___x_505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4));
v___x_506_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5);
lean_inc(v___x_500_);
v___x_507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_507_, 0, v___x_500_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
lean_inc(v___x_500_);
v___x_508_ = l_Lean_Syntax_node1(v___x_500_, v___x_504_, v___x_507_);
v___x_509_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6));
lean_inc(v___x_500_);
v___x_510_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_500_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8);
v___x_512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9));
lean_inc(v_currMacroScope_498_);
lean_inc(v_quotContext_497_);
v___x_513_ = l_Lean_addMacroScope(v_quotContext_497_, v___x_512_, v_currMacroScope_498_);
v___x_514_ = lean_box(0);
v___x_515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13));
lean_inc(v___x_500_);
v___x_516_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_516_, 0, v___x_500_);
lean_ctor_set(v___x_516_, 1, v___x_511_);
lean_ctor_set(v___x_516_, 2, v___x_513_);
lean_ctor_set(v___x_516_, 3, v___x_515_);
v___x_517_ = l_Lean_Syntax_node5(v___x_500_, v___x_501_, v___x_502_, v___x_508_, v___x_490_, v___x_510_, v___x_516_);
v___x_518_ = lean_box(0);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc(v___y_482_);
lean_inc_ref(v___y_481_);
lean_inc(v___y_480_);
lean_inc_ref(v___y_479_);
v___x_519_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(v___x_517_, v___x_518_, v___x_499_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_519_);
if (lean_obj_tag(v_a_520_) == 8)
{
lean_object* v_declName_521_; lean_object* v_type_522_; lean_object* v_value_523_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; uint8_t v___x_578_; 
v_declName_521_ = lean_ctor_get(v_a_520_, 0);
lean_inc(v_declName_521_);
v_type_522_ = lean_ctor_get(v_a_520_, 1);
lean_inc_ref(v_type_522_);
v_value_523_ = lean_ctor_get(v_a_520_, 2);
lean_inc_ref(v_value_523_);
lean_dec_ref(v_a_520_);
v___x_578_ = l_Lean_Expr_hasMVar(v_type_522_);
if (v___x_578_ == 0)
{
v___y_565_ = v___y_479_;
v___y_566_ = v___y_480_;
v___y_567_ = v___y_481_;
v___y_568_ = v___y_482_;
v___y_569_ = v___y_483_;
v___y_570_ = v___y_484_;
v___y_571_ = v___y_485_;
v___y_572_ = v___y_486_;
goto v___jp_564_;
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec_ref(v_value_523_);
lean_dec(v_declName_521_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
v___x_579_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18);
v___x_580_ = l_Lean_indentExpr(v_type_522_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_581_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v___x_582_;
}
v___jp_524_:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v_toGoalState_533_; lean_object* v_mvarId_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_555_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref(v___x_531_);
v_toGoalState_533_ = lean_ctor_get(v_a_532_, 0);
v_mvarId_534_ = lean_ctor_get(v_a_532_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_a_532_);
if (v_isSharedCheck_555_ == 0)
{
v___x_536_ = v_a_532_;
v_isShared_537_ = v_isSharedCheck_555_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_mvarId_534_);
lean_inc(v_toGoalState_533_);
lean_dec(v_a_532_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_555_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; 
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
v___x_538_ = l_Lean_MVarId_assert(v_mvarId_534_, v_declName_521_, v_type_522_, v_value_523_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref(v___x_538_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v_a_539_);
v___x_541_ = v___x_536_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_toGoalState_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_a_539_);
v___x_541_ = v_reuseFailAlloc_546_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_514_);
v___x_543_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_542_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec_ref(v___x_543_);
v___x_544_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14));
v___x_545_ = l_Lean_Elab_Tactic_Grind_liftAction___redArg(v___x_544_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_526_);
return v___x_545_;
}
else
{
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v___x_543_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_del_object(v___x_536_);
lean_dec_ref(v_toGoalState_533_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
v_a_547_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_538_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_538_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec_ref(v_value_523_);
lean_dec_ref(v_type_522_);
lean_dec(v_declName_521_);
v_a_556_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_531_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_531_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
v___jp_564_:
{
uint8_t v___x_573_; 
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
v___x_573_ = l_Lean_Expr_hasMVar(v_value_523_);
if (v___x_573_ == 0)
{
v___y_525_ = v___y_565_;
v___y_526_ = v___y_566_;
v___y_527_ = v___y_569_;
v___y_528_ = v___y_570_;
v___y_529_ = v___y_571_;
v___y_530_ = v___y_572_;
goto v___jp_524_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec_ref(v_type_522_);
lean_dec(v_declName_521_);
v___x_574_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16);
v___x_575_ = l_Lean_indentExpr(v_value_523_);
v___x_576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v___x_577_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_576_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
return v___x_577_;
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
v___x_583_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20);
v___x_584_ = l_Lean_indentExpr(v_a_520_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_585_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
return v___x_586_;
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
v_a_587_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_519_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_519_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed(lean_object* v___x_595_, lean_object* v_stx_596_, lean_object* v___x_597_, lean_object* v___x_598_, lean_object* v___x_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___x_6413__boxed_609_; lean_object* v_res_610_; 
v___x_6413__boxed_609_ = lean_unbox(v___x_595_);
v_res_610_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(v___x_6413__boxed_609_, v_stx_596_, v___x_597_, v___x_598_, v___x_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v_stx_596_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(lean_object* v_stx_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___y_638_; lean_object* v___x_639_; 
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0));
v___x_633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1));
v___x_634_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4));
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5));
lean_inc(v_stx_622_);
v___x_636_ = l_Lean_Syntax_isOfKind(v_stx_622_, v___x_635_);
v___x_637_ = lean_box(v___x_636_);
v___y_638_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed), 14, 5);
lean_closure_set(v___y_638_, 0, v___x_637_);
lean_closure_set(v___y_638_, 1, v_stx_622_);
lean_closure_set(v___y_638_, 2, v___x_632_);
lean_closure_set(v___y_638_, 3, v___x_633_);
lean_closure_set(v___y_638_, 4, v___x_634_);
v___x_639_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_638_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed(lean_object* v_stx_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(v_stx_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(lean_object* v_00_u03b1_651_, lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v_msg_652_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___boxed(lean_object* v_00_u03b1_663_, lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(v_00_u03b1_663_, v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1(){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_715_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_716_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5));
v___x_717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14));
v___x_718_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed), 10, 0);
v___x_719_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_715_, v___x_716_, v___x_717_, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___boxed(lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(uint8_t v___x_731_, lean_object* v_stx_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
if (v___x_731_ == 0)
{
lean_object* v___x_742_; 
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
v___x_742_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_742_;
}
else
{
lean_object* v___x_743_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v_id_x3f_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_900_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = l_Lean_Syntax_getArg(v_stx_732_, v___x_906_);
v___x_908_ = l_Lean_Syntax_isNone(v___x_907_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; 
lean_inc(v___x_907_);
v___x_909_ = l_Lean_Syntax_matchesNull(v___x_907_, v___x_906_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v___x_907_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
v___x_910_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_910_;
}
else
{
lean_object* v_id_x3f_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_id_x3f_911_ = l_Lean_Syntax_getArg(v___x_907_, v___x_743_);
lean_dec(v___x_907_);
v___x_912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5));
lean_inc(v_id_x3f_911_);
v___x_913_ = l_Lean_Syntax_isOfKind(v_id_x3f_911_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_dec(v_id_x3f_911_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
v___x_914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_914_;
}
else
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v_id_x3f_911_);
v_id_x3f_892_ = v___x_915_;
v___y_893_ = v___y_733_;
v___y_894_ = v___y_734_;
v___y_895_ = v___y_735_;
v___y_896_ = v___y_736_;
v___y_897_ = v___y_737_;
v___y_898_ = v___y_738_;
v___y_899_ = v___y_739_;
v___y_900_ = v___y_740_;
goto v___jp_891_;
}
}
}
else
{
lean_object* v___x_916_; 
lean_dec(v___x_907_);
v___x_916_ = lean_box(0);
v_id_x3f_892_ = v___x_916_;
v___y_893_ = v___y_733_;
v___y_894_ = v___y_734_;
v___y_895_ = v___y_735_;
v___y_896_ = v___y_736_;
v___y_897_ = v___y_737_;
v___y_898_ = v___y_738_;
v___y_899_ = v___y_739_;
v___y_900_ = v___y_740_;
goto v___jp_891_;
}
v___jp_744_:
{
lean_object* v___x_757_; lean_object* v_a_758_; lean_object* v___x_759_; 
v___x_757_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v___y_745_, v___y_754_);
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref(v___x_757_);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
v___x_759_ = l_Lean_MVarId_assert(v___y_748_, v___y_750_, v___y_749_, v_a_758_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___y_747_);
lean_ctor_set(v___x_761_, 1, v_a_760_);
v___x_762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___y_746_);
v___x_763_ = l_Lean_Elab_Tactic_Grind_setGoals___redArg(v___x_762_, v___y_752_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v___x_763_);
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14));
v___x_765_ = l_Lean_Elab_Tactic_Grind_liftAction___redArg(v___x_764_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_752_);
return v___x_765_;
}
else
{
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v___x_763_;
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
v_a_766_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_759_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_759_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
v___jp_774_:
{
lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_box(0);
v___x_786_ = 0;
lean_inc(v___y_776_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_782_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_780_);
v___x_787_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(v___y_781_, v___x_785_, v___x_786_, v___y_780_, v___y_779_, v___y_783_, v___y_775_, v___y_782_, v___y_778_, v___y_777_, v___y_776_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref(v___x_787_);
lean_inc(v_a_788_);
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_a_788_);
v___x_790_ = 0;
v___x_791_ = lean_box(0);
lean_inc_ref(v___y_782_);
v___x_792_ = l_Lean_Meta_mkFreshExprMVar(v___x_789_, v___x_790_, v___x_791_, v___y_782_, v___y_778_, v___y_777_, v___y_776_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref(v___x_792_);
v___x_794_ = l_Lean_Elab_Tactic_Grind_getGoals___redArg(v___y_779_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
if (lean_obj_tag(v_a_795_) == 1)
{
lean_object* v_head_796_; lean_object* v_tail_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_852_; 
v_head_796_ = lean_ctor_get(v_a_795_, 0);
v_tail_797_ = lean_ctor_get(v_a_795_, 1);
v_isSharedCheck_852_ = !lean_is_exclusive(v_a_795_);
if (v_isSharedCheck_852_ == 0)
{
v___x_799_ = v_a_795_;
v_isShared_800_ = v_isSharedCheck_852_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_tail_797_);
lean_inc(v_head_796_);
lean_dec(v_a_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_852_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_toGoalState_801_; lean_object* v_mvarId_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_851_; 
v_toGoalState_801_ = lean_ctor_get(v_head_796_, 0);
v_mvarId_802_ = lean_ctor_get(v_head_796_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_head_796_);
if (v_isSharedCheck_851_ == 0)
{
v___x_804_ = v_head_796_;
v_isShared_805_ = v_isSharedCheck_851_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_mvarId_802_);
lean_inc(v_toGoalState_801_);
lean_dec(v_head_796_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_851_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = l_Lean_Expr_mvarId_x21(v_a_793_);
lean_inc_ref(v_toGoalState_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 1, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_toGoalState_801_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_806_);
v___x_808_ = v_reuseFailAlloc_850_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_box(0);
lean_inc_ref(v___x_808_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v___x_809_);
lean_ctor_set(v___x_799_, 0, v___x_808_);
v___x_811_ = v___x_799_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_849_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Elab_Tactic_Grind_setGoals___redArg(v___x_811_, v___y_779_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec_ref(v___x_812_);
v___x_813_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_solve___boxed), 11, 1);
lean_closure_set(v___x_813_, 0, v___x_808_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_782_);
lean_inc_ref(v___y_780_);
v___x_814_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_813_, v___y_780_, v___y_779_, v___y_782_, v___y_778_, v___y_777_, v___y_776_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
if (lean_obj_tag(v_a_815_) == 1)
{
lean_object* v_params_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
lean_dec(v_mvarId_802_);
lean_dec_ref(v_toGoalState_801_);
lean_dec(v_tail_797_);
lean_dec(v_a_793_);
lean_dec(v_a_788_);
lean_dec(v___y_784_);
v_params_816_ = lean_ctor_get(v___y_780_, 4);
lean_inc_ref(v_params_816_);
v___x_817_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkResult___boxed), 12, 2);
lean_closure_set(v___x_817_, 0, v_params_816_);
lean_closure_set(v___x_817_, 1, v_a_815_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_782_);
v___x_818_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_817_, v___y_780_, v___y_779_, v___y_782_, v___y_778_, v___y_777_, v___y_776_);
lean_dec(v___y_779_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref(v___x_818_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_777_);
lean_inc(v___y_778_);
lean_inc_ref(v___y_782_);
v___x_820_ = l_Lean_Meta_Grind_Result_toMessageData(v_a_819_, v___y_782_, v___y_778_, v___y_777_, v___y_776_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_820_);
v___x_822_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v_a_821_);
v___x_824_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_823_, v___y_782_, v___y_778_, v___y_777_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_782_);
return v___x_824_;
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec_ref(v___y_782_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
v_a_825_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_820_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_820_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref(v___y_782_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
v_a_833_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_818_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_818_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_dec(v_a_815_);
v___y_745_ = v_a_793_;
v___y_746_ = v_tail_797_;
v___y_747_ = v_toGoalState_801_;
v___y_748_ = v_mvarId_802_;
v___y_749_ = v_a_788_;
v___y_750_ = v___y_784_;
v___y_751_ = v___y_780_;
v___y_752_ = v___y_779_;
v___y_753_ = v___y_782_;
v___y_754_ = v___y_778_;
v___y_755_ = v___y_777_;
v___y_756_ = v___y_776_;
goto v___jp_744_;
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_mvarId_802_);
lean_dec_ref(v_toGoalState_801_);
lean_dec(v_tail_797_);
lean_dec(v_a_793_);
lean_dec(v_a_788_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
v_a_841_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_814_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_814_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_dec_ref(v___x_808_);
lean_dec(v_mvarId_802_);
lean_dec_ref(v_toGoalState_801_);
lean_dec(v_tail_797_);
lean_dec(v_a_793_);
lean_dec(v_a_788_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
return v___x_812_;
}
}
}
}
}
}
else
{
lean_object* v___x_853_; 
lean_dec(v_a_795_);
lean_dec(v_a_793_);
lean_dec(v_a_788_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
v___x_853_ = l_Lean_Elab_Tactic_Grind_throwNoGoalsToBeSolved___redArg(v___y_782_, v___y_778_, v___y_777_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_782_);
return v___x_853_;
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_a_793_);
lean_dec(v_a_788_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
v_a_854_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_794_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_794_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_788_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
v_a_862_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_792_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_792_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v___y_784_);
lean_dec_ref(v___y_782_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
v_a_870_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_787_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_787_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
v___jp_878_:
{
uint8_t v___x_889_; 
v___x_889_ = l_Lean_Name_hasMacroScopes(v___y_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Grind_markGrindName(v___y_888_);
v___y_775_ = v___y_879_;
v___y_776_ = v___y_880_;
v___y_777_ = v___y_882_;
v___y_778_ = v___y_881_;
v___y_779_ = v___y_883_;
v___y_780_ = v___y_885_;
v___y_781_ = v___y_884_;
v___y_782_ = v___y_887_;
v___y_783_ = v___y_886_;
v___y_784_ = v___x_890_;
goto v___jp_774_;
}
else
{
v___y_775_ = v___y_879_;
v___y_776_ = v___y_880_;
v___y_777_ = v___y_882_;
v___y_778_ = v___y_881_;
v___y_779_ = v___y_883_;
v___y_780_ = v___y_885_;
v___y_781_ = v___y_884_;
v___y_782_ = v___y_887_;
v___y_783_ = v___y_886_;
v___y_784_ = v___y_888_;
goto v___jp_774_;
}
}
v___jp_891_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(3u);
v___x_902_ = l_Lean_Syntax_getArg(v_stx_732_, v___x_901_);
if (lean_obj_tag(v_id_x3f_892_) == 1)
{
lean_object* v_val_903_; lean_object* v___x_904_; 
v_val_903_ = lean_ctor_get(v_id_x3f_892_, 0);
lean_inc(v_val_903_);
lean_dec_ref(v_id_x3f_892_);
v___x_904_ = l_Lean_TSyntax_getId(v_val_903_);
lean_dec(v_val_903_);
v___y_879_ = v___y_896_;
v___y_880_ = v___y_900_;
v___y_881_ = v___y_898_;
v___y_882_ = v___y_899_;
v___y_883_ = v___y_894_;
v___y_884_ = v___x_902_;
v___y_885_ = v___y_893_;
v___y_886_ = v___y_895_;
v___y_887_ = v___y_897_;
v___y_888_ = v___x_904_;
goto v___jp_878_;
}
else
{
lean_object* v___x_905_; 
lean_dec(v_id_x3f_892_);
v___x_905_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3));
v___y_879_ = v___y_896_;
v___y_880_ = v___y_900_;
v___y_881_ = v___y_898_;
v___y_882_ = v___y_899_;
v___y_883_ = v___y_894_;
v___y_884_ = v___x_902_;
v___y_885_ = v___y_893_;
v___y_886_ = v___y_895_;
v___y_887_ = v___y_897_;
v___y_888_ = v___x_905_;
goto v___jp_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed(lean_object* v___x_917_, lean_object* v_stx_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
uint8_t v___x_3717__boxed_928_; lean_object* v_res_929_; 
v___x_3717__boxed_928_ = lean_unbox(v___x_917_);
v_res_929_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(v___x_3717__boxed_928_, v_stx_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v_stx_918_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(lean_object* v_stx_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___y_950_; lean_object* v___x_951_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1));
lean_inc(v_stx_937_);
v___x_948_ = l_Lean_Syntax_isOfKind(v_stx_937_, v___x_947_);
v___x_949_ = lean_box(v___x_948_);
v___y_950_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed), 11, 2);
lean_closure_set(v___y_950_, 0, v___x_949_);
lean_closure_set(v___y_950_, 1, v_stx_937_);
v___x_951_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_950_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed(lean_object* v_stx_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(v_stx_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1(){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_968_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1));
v___x_970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1));
v___x_971_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed), 10, 0);
v___x_972_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_968_, v___x_969_, v___x_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___boxed(lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
return v_res_974_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Have(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Have(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Solve(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Have(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Have(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Have(builtin);
}
#ifdef __cplusplus
}
#endif
