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
v___x_65_ = l_Lean_Elab_Term_elabTerm(v_stx_52_, v_expectedType_x3f_53_, v___x_64_, v___x_64_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; uint8_t v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_65_);
v___x_67_ = l_Lean_Elab_Term_PostponeBehavior_ofBool(v_mayPostpone_54_);
v___x_68_ = 0;
v___x_69_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_67_, v___x_68_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v___x_70_; 
lean_dec_ref(v___x_69_);
v___x_70_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v_a_66_, v_a_60_);
return v___x_70_;
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
lean_dec(v_a_66_);
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
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec_ref(v_a_84_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(lean_object* v_a_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
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
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
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
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
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
lean_object* v_options_177_; lean_object* v_declName_x3f_178_; lean_object* v_macroStack_179_; uint8_t v_mayPostpone_180_; uint8_t v_errToSorry_181_; lean_object* v_autoBoundImplicitContext_182_; lean_object* v_autoBoundImplicitForbidden_183_; lean_object* v_sectionVars_184_; lean_object* v_sectionFVars_185_; uint8_t v_implicitLambda_186_; uint8_t v_heedElabAsElim_187_; uint8_t v_isNoncomputableSection_188_; uint8_t v_isMetaSection_189_; uint8_t v_ignoreTCFailures_190_; uint8_t v_inPattern_191_; lean_object* v_tacSnap_x3f_192_; uint8_t v_saveRecAppSyntax_193_; uint8_t v_holesAsSyntheticOpaque_194_; uint8_t v_checkDeprecated_195_; lean_object* v_fixedTermElabs_196_; lean_object* v___y_198_; uint8_t v___y_202_; 
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
v_isMetaSection_189_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 5);
v_ignoreTCFailures_190_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 6);
v_inPattern_191_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_192_ = lean_ctor_get(v___y_170_, 6);
v_saveRecAppSyntax_193_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_194_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 9);
v_checkDeprecated_195_ = lean_ctor_get_uint8(v___y_170_, sizeof(void*)*8 + 10);
v_fixedTermElabs_196_ = lean_ctor_get(v___y_170_, 7);
if (lean_obj_tag(v_tacSnap_x3f_192_) == 0)
{
v___y_198_ = v_tacSnap_x3f_192_;
goto v___jp_197_;
}
else
{
lean_object* v_val_204_; lean_object* v_old_x3f_205_; lean_object* v___x_206_; lean_object* v___f_207_; 
v_val_204_ = lean_ctor_get(v_tacSnap_x3f_192_, 0);
v_old_x3f_205_ = lean_ctor_get(v_val_204_, 0);
v___x_206_ = lean_box(v_cond_166_);
v___f_207_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_207_, 0, v___x_206_);
if (lean_obj_tag(v_old_x3f_205_) == 1)
{
if (v_cond_166_ == 0)
{
lean_dec_ref(v___f_207_);
goto v___jp_208_;
}
else
{
lean_object* v_val_211_; lean_object* v_map_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_val_211_ = lean_ctor_get(v_old_x3f_205_, 0);
v_map_212_ = lean_ctor_get(v_options_177_, 0);
v___x_213_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3));
v___x_214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_212_, v___x_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_dec_ref(v___f_207_);
goto v___jp_208_;
}
else
{
lean_object* v_val_215_; 
v_val_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_215_);
lean_dec_ref(v___x_214_);
if (lean_obj_tag(v_val_215_) == 1)
{
uint8_t v_v_216_; 
v_v_216_ = lean_ctor_get_uint8(v_val_215_, 0);
lean_dec_ref(v_val_215_);
if (v_v_216_ == 0)
{
lean_dec_ref(v___f_207_);
goto v___jp_208_;
}
else
{
lean_object* v_stx_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_stx_217_ = lean_ctor_get(v_val_211_, 0);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_218_, 0, v___f_207_);
v___x_219_ = ((lean_object*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4));
v___x_220_ = lean_box(0);
v___x_221_ = 0;
lean_inc(v_stx_217_);
v___x_222_ = l_Lean_Syntax_formatStx(v_stx_217_, v___x_220_, v___x_221_);
v___x_223_ = l_Std_Format_defWidth;
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l_Std_Format_pretty(v___x_222_, v___x_223_, v___x_224_, v___x_224_);
v___x_226_ = lean_string_append(v___x_219_, v___x_225_);
lean_dec_ref(v___x_225_);
v___x_227_ = lean_dbg_trace(v___x_226_, v___f_218_);
v___x_228_ = lean_unbox(v___x_227_);
lean_dec(v___x_227_);
v___y_202_ = v___x_228_;
goto v___jp_201_;
}
}
else
{
lean_dec(v_val_215_);
lean_dec_ref(v___f_207_);
goto v___jp_208_;
}
}
}
}
else
{
lean_object* v___x_229_; uint8_t v___x_230_; 
lean_dec_ref(v___f_207_);
v___x_229_ = lean_box(0);
v___x_230_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_166_, v___x_229_);
v___y_202_ = v___x_230_;
goto v___jp_201_;
}
v___jp_208_:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_box(0);
v___x_210_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_166_, v___x_209_);
v___y_202_ = v___x_210_;
goto v___jp_201_;
}
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_inc_ref(v_fixedTermElabs_196_);
lean_inc(v_sectionFVars_185_);
lean_inc(v_sectionVars_184_);
lean_inc_ref(v_autoBoundImplicitForbidden_183_);
lean_inc(v_autoBoundImplicitContext_182_);
lean_inc(v_macroStack_179_);
lean_inc(v_declName_x3f_178_);
v___x_199_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_199_, 0, v_declName_x3f_178_);
lean_ctor_set(v___x_199_, 1, v_macroStack_179_);
lean_ctor_set(v___x_199_, 2, v_autoBoundImplicitContext_182_);
lean_ctor_set(v___x_199_, 3, v_autoBoundImplicitForbidden_183_);
lean_ctor_set(v___x_199_, 4, v_sectionVars_184_);
lean_ctor_set(v___x_199_, 5, v_sectionFVars_185_);
lean_ctor_set(v___x_199_, 6, v___y_198_);
lean_ctor_set(v___x_199_, 7, v_fixedTermElabs_196_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8, v_mayPostpone_180_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 1, v_errToSorry_181_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 2, v_implicitLambda_186_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 3, v_heedElabAsElim_187_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 4, v_isNoncomputableSection_188_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 5, v_isMetaSection_189_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 6, v_ignoreTCFailures_190_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 7, v_inPattern_191_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_193_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_194_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*8 + 10, v_checkDeprecated_195_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
v___x_200_ = lean_apply_9(v_act_167_, v___y_168_, v___y_169_, v___x_199_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, lean_box(0));
return v___x_200_;
}
v___jp_201_:
{
if (v___y_202_ == 0)
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
v___y_198_ = v___x_203_;
goto v___jp_197_;
}
else
{
lean_inc(v_tacSnap_x3f_192_);
v___y_198_ = v_tacSnap_x3f_192_;
goto v___jp_197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(lean_object* v_cond_231_, lean_object* v_act_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
uint8_t v_cond_boxed_242_; lean_object* v_res_243_; 
v_cond_boxed_242_ = lean_unbox(v_cond_231_);
v_res_243_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v_cond_boxed_242_, v_act_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(lean_object* v_00_u03b1_244_, uint8_t v_cond_245_, lean_object* v_act_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v_cond_245_, v_act_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(lean_object* v_00_u03b1_257_, lean_object* v_cond_258_, lean_object* v_act_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
uint8_t v_cond_boxed_269_; lean_object* v_res_270_; 
v_cond_boxed_269_ = lean_unbox(v_cond_258_);
v_res_270_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(v_00_u03b1_257_, v_cond_boxed_269_, v_act_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(lean_object* v_stx_271_, lean_object* v_expectedType_x3f_272_, uint8_t v_mayPostpone_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_toContext_283_; uint8_t v_recover_284_; 
v_toContext_283_ = lean_ctor_get(v___y_274_, 0);
v_recover_284_ = lean_ctor_get_uint8(v_toContext_283_, sizeof(void*)*1);
if (v_recover_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(v_mayPostpone_273_);
v___x_286_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed), 12, 3);
lean_closure_set(v___x_286_, 0, v_stx_271_);
lean_closure_set(v___x_286_, 1, v_expectedType_x3f_272_);
lean_closure_set(v___x_286_, 2, v___x_285_);
v___x_287_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(v___x_286_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(v_stx_271_, v_expectedType_x3f_272_, v_mayPostpone_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(lean_object* v_stx_289_, lean_object* v_expectedType_x3f_290_, lean_object* v_mayPostpone_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
uint8_t v_mayPostpone_boxed_301_; lean_object* v_res_302_; 
v_mayPostpone_boxed_301_ = lean_unbox(v_mayPostpone_291_);
v_res_302_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(v_stx_289_, v_expectedType_x3f_290_, v_mayPostpone_boxed_301_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(lean_object* v_stx_303_, lean_object* v_expectedType_x3f_304_, uint8_t v_mayPostpone_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_fileName_315_; lean_object* v_fileMap_316_; lean_object* v_options_317_; lean_object* v_currRecDepth_318_; lean_object* v_maxRecDepth_319_; lean_object* v_ref_320_; lean_object* v_currNamespace_321_; lean_object* v_openDecls_322_; lean_object* v_initHeartbeats_323_; lean_object* v_maxHeartbeats_324_; lean_object* v_quotContext_325_; lean_object* v_currMacroScope_326_; uint8_t v_diag_327_; lean_object* v_cancelTk_x3f_328_; uint8_t v_suppressElabErrors_329_; lean_object* v_inheritedTraceOptions_330_; lean_object* v___x_331_; lean_object* v___f_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v_ref_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_fileName_315_ = lean_ctor_get(v_a_312_, 0);
v_fileMap_316_ = lean_ctor_get(v_a_312_, 1);
v_options_317_ = lean_ctor_get(v_a_312_, 2);
v_currRecDepth_318_ = lean_ctor_get(v_a_312_, 3);
v_maxRecDepth_319_ = lean_ctor_get(v_a_312_, 4);
v_ref_320_ = lean_ctor_get(v_a_312_, 5);
v_currNamespace_321_ = lean_ctor_get(v_a_312_, 6);
v_openDecls_322_ = lean_ctor_get(v_a_312_, 7);
v_initHeartbeats_323_ = lean_ctor_get(v_a_312_, 8);
v_maxHeartbeats_324_ = lean_ctor_get(v_a_312_, 9);
v_quotContext_325_ = lean_ctor_get(v_a_312_, 10);
v_currMacroScope_326_ = lean_ctor_get(v_a_312_, 11);
v_diag_327_ = lean_ctor_get_uint8(v_a_312_, sizeof(void*)*14);
v_cancelTk_x3f_328_ = lean_ctor_get(v_a_312_, 12);
v_suppressElabErrors_329_ = lean_ctor_get_uint8(v_a_312_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_330_ = lean_ctor_get(v_a_312_, 13);
v___x_331_ = lean_box(v_mayPostpone_305_);
lean_inc(v_stx_303_);
v___f_332_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed), 12, 3);
lean_closure_set(v___f_332_, 0, v_stx_303_);
lean_closure_set(v___f_332_, 1, v_expectedType_x3f_304_);
lean_closure_set(v___f_332_, 2, v___x_331_);
v___x_333_ = 1;
v___x_334_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withMainContext___boxed), 11, 2);
lean_closure_set(v___x_334_, 0, lean_box(0));
lean_closure_set(v___x_334_, 1, v___f_332_);
v_ref_335_ = l_Lean_replaceRef(v_stx_303_, v_ref_320_);
lean_dec(v_stx_303_);
lean_inc_ref(v_inheritedTraceOptions_330_);
lean_inc(v_cancelTk_x3f_328_);
lean_inc(v_currMacroScope_326_);
lean_inc(v_quotContext_325_);
lean_inc(v_maxHeartbeats_324_);
lean_inc(v_initHeartbeats_323_);
lean_inc(v_openDecls_322_);
lean_inc(v_currNamespace_321_);
lean_inc(v_maxRecDepth_319_);
lean_inc(v_currRecDepth_318_);
lean_inc_ref(v_options_317_);
lean_inc_ref(v_fileMap_316_);
lean_inc_ref(v_fileName_315_);
v___x_336_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_336_, 0, v_fileName_315_);
lean_ctor_set(v___x_336_, 1, v_fileMap_316_);
lean_ctor_set(v___x_336_, 2, v_options_317_);
lean_ctor_set(v___x_336_, 3, v_currRecDepth_318_);
lean_ctor_set(v___x_336_, 4, v_maxRecDepth_319_);
lean_ctor_set(v___x_336_, 5, v_ref_335_);
lean_ctor_set(v___x_336_, 6, v_currNamespace_321_);
lean_ctor_set(v___x_336_, 7, v_openDecls_322_);
lean_ctor_set(v___x_336_, 8, v_initHeartbeats_323_);
lean_ctor_set(v___x_336_, 9, v_maxHeartbeats_324_);
lean_ctor_set(v___x_336_, 10, v_quotContext_325_);
lean_ctor_set(v___x_336_, 11, v_currMacroScope_326_);
lean_ctor_set(v___x_336_, 12, v_cancelTk_x3f_328_);
lean_ctor_set(v___x_336_, 13, v_inheritedTraceOptions_330_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*14, v_diag_327_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*14 + 1, v_suppressElabErrors_329_);
v___x_337_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v___x_333_, v___x_334_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v___x_336_, v_a_313_);
lean_dec_ref(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(lean_object* v_stx_338_, lean_object* v_expectedType_x3f_339_, lean_object* v_mayPostpone_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
uint8_t v_mayPostpone_boxed_350_; lean_object* v_res_351_; 
v_mayPostpone_boxed_350_ = lean_unbox(v_mayPostpone_340_);
v_res_351_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(v_stx_338_, v_expectedType_x3f_339_, v_mayPostpone_boxed_350_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_box(0);
v___x_353_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg(){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___boxed(lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(lean_object* v_00_u03b1_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(lean_object* v_00_u03b1_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(v_00_u03b1_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(lean_object* v_msgData_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v_env_389_; lean_object* v___x_390_; lean_object* v_mctx_391_; lean_object* v_lctx_392_; lean_object* v_options_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_388_ = lean_st_ref_get(v___y_386_);
v_env_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_388_);
v___x_390_ = lean_st_ref_get(v___y_384_);
v_mctx_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_mctx_391_);
lean_dec(v___x_390_);
v_lctx_392_ = lean_ctor_get(v___y_383_, 2);
v_options_393_ = lean_ctor_get(v___y_385_, 2);
lean_inc_ref(v_options_393_);
lean_inc_ref(v_lctx_392_);
v___x_394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_394_, 0, v_env_389_);
lean_ctor_set(v___x_394_, 1, v_mctx_391_);
lean_ctor_set(v___x_394_, 2, v_lctx_392_);
lean_ctor_set(v___x_394_, 3, v_options_393_);
v___x_395_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_msgData_382_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1___boxed(lean_object* v_msgData_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(v_msgData_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_ref_410_; lean_object* v___x_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_ref_410_ = lean_ctor_get(v___y_407_, 5);
v___x_411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc(v_ref_410_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_ref_410_);
lean_ctor_set(v___x_416_, 1, v_a_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 1);
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___boxed(lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v_msg_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_427_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5(void){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Array_mkArray0(lean_box(0));
return v___x_434_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7));
v___x_438_ = l_String_toRawSubstring_x27(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(uint8_t v___x_463_, lean_object* v_stx_464_, lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
if (v___x_463_ == 0)
{
lean_object* v___x_477_; 
lean_dec_ref(v___x_467_);
lean_dec_ref(v___x_466_);
lean_dec_ref(v___x_465_);
v___x_477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = l_Lean_Syntax_getArg(v_stx_464_, v___x_478_);
v___x_480_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0));
v___x_481_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1));
lean_inc_ref(v___x_466_);
lean_inc_ref(v___x_465_);
v___x_482_ = l_Lean_Name_mkStr4(v___x_465_, v___x_466_, v___x_480_, v___x_481_);
lean_inc(v___x_479_);
v___x_483_ = l_Lean_Syntax_isOfKind(v___x_479_, v___x_482_);
lean_dec(v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec(v___x_479_);
lean_dec_ref(v___x_467_);
lean_dec_ref(v___x_466_);
lean_dec_ref(v___x_465_);
v___x_484_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_484_;
}
else
{
lean_object* v_ref_485_; lean_object* v_quotContext_486_; lean_object* v_currMacroScope_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_ref_485_ = lean_ctor_get(v___y_474_, 5);
v_quotContext_486_ = lean_ctor_get(v___y_474_, 10);
v_currMacroScope_487_ = lean_ctor_get(v___y_474_, 11);
v___x_488_ = 0;
v___x_489_ = l_Lean_SourceInfo_fromRef(v_ref_485_, v___x_488_);
lean_inc_ref(v___x_467_);
lean_inc_ref(v___x_466_);
lean_inc_ref(v___x_465_);
v___x_490_ = l_Lean_Name_mkStr4(v___x_465_, v___x_466_, v___x_480_, v___x_467_);
lean_inc_n(v___x_489_, 5);
v___x_491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_467_);
v___x_492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2));
v___x_493_ = l_Lean_Name_mkStr4(v___x_465_, v___x_466_, v___x_480_, v___x_492_);
v___x_494_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4));
v___x_495_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5);
v___x_496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_496_, 0, v___x_489_);
lean_ctor_set(v___x_496_, 1, v___x_494_);
lean_ctor_set(v___x_496_, 2, v___x_495_);
v___x_497_ = l_Lean_Syntax_node1(v___x_489_, v___x_493_, v___x_496_);
v___x_498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6));
v___x_499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_489_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8);
v___x_501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9));
lean_inc(v_currMacroScope_487_);
lean_inc(v_quotContext_486_);
v___x_502_ = l_Lean_addMacroScope(v_quotContext_486_, v___x_501_, v_currMacroScope_487_);
v___x_503_ = lean_box(0);
v___x_504_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13));
v___x_505_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_505_, 0, v___x_489_);
lean_ctor_set(v___x_505_, 1, v___x_500_);
lean_ctor_set(v___x_505_, 2, v___x_502_);
lean_ctor_set(v___x_505_, 3, v___x_504_);
v___x_506_ = l_Lean_Syntax_node5(v___x_489_, v___x_490_, v___x_491_, v___x_497_, v___x_479_, v___x_499_, v___x_505_);
v___x_507_ = lean_box(0);
v___x_508_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(v___x_506_, v___x_507_, v___x_488_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref(v___x_508_);
if (lean_obj_tag(v_a_509_) == 8)
{
lean_object* v_declName_510_; lean_object* v_type_511_; lean_object* v_value_512_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; uint8_t v___x_567_; 
v_declName_510_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_declName_510_);
v_type_511_ = lean_ctor_get(v_a_509_, 1);
lean_inc_ref(v_type_511_);
v_value_512_ = lean_ctor_get(v_a_509_, 2);
lean_inc_ref(v_value_512_);
lean_dec_ref(v_a_509_);
v___x_567_ = l_Lean_Expr_hasMVar(v_type_511_);
if (v___x_567_ == 0)
{
v___y_554_ = v___y_468_;
v___y_555_ = v___y_469_;
v___y_556_ = v___y_470_;
v___y_557_ = v___y_471_;
v___y_558_ = v___y_472_;
v___y_559_ = v___y_473_;
v___y_560_ = v___y_474_;
v___y_561_ = v___y_475_;
goto v___jp_553_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v_value_512_);
lean_dec(v_declName_510_);
v___x_568_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18);
v___x_569_ = l_Lean_indentExpr(v_type_511_);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_570_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_571_;
}
v___jp_513_:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v_toGoalState_522_; lean_object* v_mvarId_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_544_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_520_);
v_toGoalState_522_ = lean_ctor_get(v_a_521_, 0);
v_mvarId_523_ = lean_ctor_get(v_a_521_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_521_);
if (v_isSharedCheck_544_ == 0)
{
v___x_525_ = v_a_521_;
v_isShared_526_ = v_isSharedCheck_544_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_mvarId_523_);
lean_inc(v_toGoalState_522_);
lean_dec(v_a_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_544_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_MVarId_assert(v_mvarId_523_, v_declName_510_, v_type_511_, v_value_512_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_530_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_a_528_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_toGoalState_522_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_528_);
v___x_530_ = v_reuseFailAlloc_535_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_503_);
v___x_532_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v___x_531_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec_ref(v___x_532_);
v___x_533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14));
v___x_534_ = l_Lean_Elab_Tactic_Grind_liftAction___redArg(v___x_533_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
return v___x_534_;
}
else
{
return v___x_532_;
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_del_object(v___x_525_);
lean_dec_ref(v_toGoalState_522_);
v_a_536_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_527_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_527_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_value_512_);
lean_dec_ref(v_type_511_);
lean_dec(v_declName_510_);
v_a_545_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_520_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_520_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
v___jp_553_:
{
uint8_t v___x_562_; 
v___x_562_ = l_Lean_Expr_hasMVar(v_value_512_);
if (v___x_562_ == 0)
{
v___y_514_ = v___y_554_;
v___y_515_ = v___y_555_;
v___y_516_ = v___y_558_;
v___y_517_ = v___y_559_;
v___y_518_ = v___y_560_;
v___y_519_ = v___y_561_;
goto v___jp_513_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_type_511_);
lean_dec(v_declName_510_);
v___x_563_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16);
v___x_564_ = l_Lean_indentExpr(v_value_512_);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_565_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
return v___x_566_;
}
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_572_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20);
v___x_573_ = l_Lean_indentExpr(v_a_509_);
v___x_574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_574_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
return v___x_575_;
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
v_a_576_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_508_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_508_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed(lean_object* v___x_584_, lean_object* v_stx_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
uint8_t v___x_6380__boxed_598_; lean_object* v_res_599_; 
v___x_6380__boxed_598_ = lean_unbox(v___x_584_);
v_res_599_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(v___x_6380__boxed_598_, v_stx_585_, v___x_586_, v___x_587_, v___x_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v_stx_585_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(lean_object* v_stx_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___y_627_; lean_object* v___x_628_; 
v___x_621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0));
v___x_622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1));
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4));
v___x_624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5));
lean_inc(v_stx_611_);
v___x_625_ = l_Lean_Syntax_isOfKind(v_stx_611_, v___x_624_);
v___x_626_ = lean_box(v___x_625_);
v___y_627_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed), 14, 5);
lean_closure_set(v___y_627_, 0, v___x_626_);
lean_closure_set(v___y_627_, 1, v_stx_611_);
lean_closure_set(v___y_627_, 2, v___x_621_);
lean_closure_set(v___y_627_, 3, v___x_622_);
lean_closure_set(v___y_627_, 4, v___x_623_);
v___x_628_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_627_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed(lean_object* v_stx_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(v_stx_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(lean_object* v_00_u03b1_640_, lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v_msg_641_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___boxed(lean_object* v_00_u03b1_652_, lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(v_00_u03b1_652_, v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1(){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_705_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5));
v___x_706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14));
v___x_707_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed), 10, 0);
v___x_708_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_704_, v___x_705_, v___x_706_, v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
return v_res_710_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0));
v___x_713_ = l_Lean_stringToMessageData(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(uint8_t v___x_720_, lean_object* v_stx_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
if (v___x_720_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v_id_x3f_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = l_Lean_Syntax_getArg(v_stx_721_, v___x_895_);
v___x_897_ = l_Lean_Syntax_isNone(v___x_896_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; 
lean_inc(v___x_896_);
v___x_898_ = l_Lean_Syntax_matchesNull(v___x_896_, v___x_895_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec(v___x_896_);
v___x_899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_899_;
}
else
{
lean_object* v_id_x3f_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_id_x3f_900_ = l_Lean_Syntax_getArg(v___x_896_, v___x_732_);
lean_dec(v___x_896_);
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5));
lean_inc(v_id_x3f_900_);
v___x_902_ = l_Lean_Syntax_isOfKind(v_id_x3f_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v_id_x3f_900_);
v___x_903_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return v___x_903_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v_id_x3f_900_);
v_id_x3f_881_ = v___x_904_;
v___y_882_ = v___y_722_;
v___y_883_ = v___y_723_;
v___y_884_ = v___y_724_;
v___y_885_ = v___y_725_;
v___y_886_ = v___y_726_;
v___y_887_ = v___y_727_;
v___y_888_ = v___y_728_;
v___y_889_ = v___y_729_;
goto v___jp_880_;
}
}
}
else
{
lean_object* v___x_905_; 
lean_dec(v___x_896_);
v___x_905_ = lean_box(0);
v_id_x3f_881_ = v___x_905_;
v___y_882_ = v___y_722_;
v___y_883_ = v___y_723_;
v___y_884_ = v___y_724_;
v___y_885_ = v___y_725_;
v___y_886_ = v___y_726_;
v___y_887_ = v___y_727_;
v___y_888_ = v___y_728_;
v___y_889_ = v___y_729_;
goto v___jp_880_;
}
v___jp_733_:
{
lean_object* v___x_746_; lean_object* v_a_747_; lean_object* v___x_748_; 
v___x_746_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v___y_738_, v___y_743_);
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref(v___x_746_);
v___x_748_ = l_Lean_MVarId_assert(v___y_736_, v___y_735_, v___y_739_, v_a_747_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref(v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___y_734_);
lean_ctor_set(v___x_750_, 1, v_a_749_);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___y_737_);
v___x_752_ = l_Lean_Elab_Tactic_Grind_setGoals___redArg(v___x_751_, v___y_741_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v___x_752_);
v___x_753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14));
v___x_754_ = l_Lean_Elab_Tactic_Grind_liftAction___redArg(v___x_753_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
return v___x_754_;
}
else
{
return v___x_752_;
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v___y_737_);
lean_dec_ref(v___y_734_);
v_a_755_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_748_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_748_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
v___jp_763_:
{
lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_box(0);
v___x_775_ = 0;
v___x_776_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(v___y_771_, v___x_774_, v___x_775_, v___y_766_, v___y_772_, v___y_770_, v___y_769_, v___y_764_, v___y_768_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc_n(v_a_777_, 2);
lean_dec_ref(v___x_776_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_a_777_);
v___x_779_ = 0;
v___x_780_ = lean_box(0);
v___x_781_ = l_Lean_Meta_mkFreshExprMVar(v___x_778_, v___x_779_, v___x_780_, v___y_764_, v___y_768_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
v___x_783_ = l_Lean_Elab_Tactic_Grind_getGoals___redArg(v___y_772_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
if (lean_obj_tag(v_a_784_) == 1)
{
lean_object* v_head_785_; lean_object* v_tail_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_841_; 
v_head_785_ = lean_ctor_get(v_a_784_, 0);
v_tail_786_ = lean_ctor_get(v_a_784_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_784_);
if (v_isSharedCheck_841_ == 0)
{
v___x_788_ = v_a_784_;
v_isShared_789_ = v_isSharedCheck_841_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_tail_786_);
lean_inc(v_head_785_);
lean_dec(v_a_784_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_841_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_toGoalState_790_; lean_object* v_mvarId_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_840_; 
v_toGoalState_790_ = lean_ctor_get(v_head_785_, 0);
v_mvarId_791_ = lean_ctor_get(v_head_785_, 1);
v_isSharedCheck_840_ = !lean_is_exclusive(v_head_785_);
if (v_isSharedCheck_840_ == 0)
{
v___x_793_ = v_head_785_;
v_isShared_794_ = v_isSharedCheck_840_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_mvarId_791_);
lean_inc(v_toGoalState_790_);
lean_dec(v_head_785_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_840_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_Expr_mvarId_x21(v_a_782_);
lean_inc_ref(v_toGoalState_790_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_toGoalState_790_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_795_);
v___x_797_ = v_reuseFailAlloc_839_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_box(0);
lean_inc_ref(v___x_797_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v___x_798_);
lean_ctor_set(v___x_788_, 0, v___x_797_);
v___x_800_ = v___x_788_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_838_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Elab_Tactic_Grind_setGoals___redArg(v___x_800_, v___y_772_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v___x_801_);
v___x_802_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_solve___boxed), 11, 1);
lean_closure_set(v___x_802_, 0, v___x_797_);
v___x_803_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_802_, v___y_766_, v___y_772_, v___y_764_, v___y_768_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref(v___x_803_);
if (lean_obj_tag(v_a_804_) == 1)
{
lean_object* v_params_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v_mvarId_791_);
lean_dec_ref(v_toGoalState_790_);
lean_dec(v_tail_786_);
lean_dec(v_a_782_);
lean_dec(v_a_777_);
lean_dec(v___y_773_);
v_params_805_ = lean_ctor_get(v___y_766_, 4);
lean_inc_ref(v_params_805_);
v___x_806_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkResult___boxed), 12, 2);
lean_closure_set(v___x_806_, 0, v_params_805_);
lean_closure_set(v___x_806_, 1, v_a_804_);
v___x_807_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___x_806_, v___y_766_, v___y_772_, v___y_764_, v___y_768_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
v___x_809_ = l_Lean_Meta_Grind_Result_toMessageData(v_a_808_, v___y_764_, v___y_768_, v___y_765_, v___y_767_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref(v___x_809_);
v___x_811_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_a_810_);
v___x_813_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_812_, v___y_764_, v___y_768_, v___y_765_, v___y_767_);
return v___x_813_;
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
v_a_814_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_809_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_809_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_822_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_807_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_807_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_dec(v_a_804_);
v___y_734_ = v_toGoalState_790_;
v___y_735_ = v___y_773_;
v___y_736_ = v_mvarId_791_;
v___y_737_ = v_tail_786_;
v___y_738_ = v_a_782_;
v___y_739_ = v_a_777_;
v___y_740_ = v___y_766_;
v___y_741_ = v___y_772_;
v___y_742_ = v___y_764_;
v___y_743_ = v___y_768_;
v___y_744_ = v___y_765_;
v___y_745_ = v___y_767_;
goto v___jp_733_;
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_mvarId_791_);
lean_dec_ref(v_toGoalState_790_);
lean_dec(v_tail_786_);
lean_dec(v_a_782_);
lean_dec(v_a_777_);
lean_dec(v___y_773_);
v_a_830_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_803_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_803_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_dec_ref(v___x_797_);
lean_dec(v_mvarId_791_);
lean_dec_ref(v_toGoalState_790_);
lean_dec(v_tail_786_);
lean_dec(v_a_782_);
lean_dec(v_a_777_);
lean_dec(v___y_773_);
return v___x_801_;
}
}
}
}
}
}
else
{
lean_object* v___x_842_; 
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_dec(v_a_777_);
lean_dec(v___y_773_);
v___x_842_ = l_Lean_Elab_Tactic_Grind_throwNoGoalsToBeSolved___redArg(v___y_764_, v___y_768_, v___y_765_, v___y_767_);
return v___x_842_;
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_782_);
lean_dec(v_a_777_);
lean_dec(v___y_773_);
v_a_843_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_783_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_783_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v_a_777_);
lean_dec(v___y_773_);
v_a_851_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_781_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_781_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v___y_773_);
v_a_859_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_776_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_776_);
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
v___jp_867_:
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_Name_hasMacroScopes(v___y_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_Grind_markGrindName(v___y_877_);
v___y_764_ = v___y_868_;
v___y_765_ = v___y_870_;
v___y_766_ = v___y_869_;
v___y_767_ = v___y_871_;
v___y_768_ = v___y_872_;
v___y_769_ = v___y_873_;
v___y_770_ = v___y_874_;
v___y_771_ = v___y_875_;
v___y_772_ = v___y_876_;
v___y_773_ = v___x_879_;
goto v___jp_763_;
}
else
{
v___y_764_ = v___y_868_;
v___y_765_ = v___y_870_;
v___y_766_ = v___y_869_;
v___y_767_ = v___y_871_;
v___y_768_ = v___y_872_;
v___y_769_ = v___y_873_;
v___y_770_ = v___y_874_;
v___y_771_ = v___y_875_;
v___y_772_ = v___y_876_;
v___y_773_ = v___y_877_;
goto v___jp_763_;
}
}
v___jp_880_:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_unsigned_to_nat(3u);
v___x_891_ = l_Lean_Syntax_getArg(v_stx_721_, v___x_890_);
if (lean_obj_tag(v_id_x3f_881_) == 1)
{
lean_object* v_val_892_; lean_object* v___x_893_; 
v_val_892_ = lean_ctor_get(v_id_x3f_881_, 0);
lean_inc(v_val_892_);
lean_dec_ref(v_id_x3f_881_);
v___x_893_ = l_Lean_TSyntax_getId(v_val_892_);
lean_dec(v_val_892_);
v___y_868_ = v___y_886_;
v___y_869_ = v___y_882_;
v___y_870_ = v___y_888_;
v___y_871_ = v___y_889_;
v___y_872_ = v___y_887_;
v___y_873_ = v___y_885_;
v___y_874_ = v___y_884_;
v___y_875_ = v___x_891_;
v___y_876_ = v___y_883_;
v___y_877_ = v___x_893_;
goto v___jp_867_;
}
else
{
lean_object* v___x_894_; 
lean_dec(v_id_x3f_881_);
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3));
v___y_868_ = v___y_886_;
v___y_869_ = v___y_882_;
v___y_870_ = v___y_888_;
v___y_871_ = v___y_889_;
v___y_872_ = v___y_887_;
v___y_873_ = v___y_885_;
v___y_874_ = v___y_884_;
v___y_875_ = v___x_891_;
v___y_876_ = v___y_883_;
v___y_877_ = v___x_894_;
goto v___jp_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed(lean_object* v___x_906_, lean_object* v_stx_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
uint8_t v___x_3680__boxed_917_; lean_object* v_res_918_; 
v___x_3680__boxed_917_ = lean_unbox(v___x_906_);
v_res_918_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(v___x_3680__boxed_917_, v_stx_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v_stx_907_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(lean_object* v_stx_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___y_939_; lean_object* v___x_940_; 
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1));
lean_inc(v_stx_926_);
v___x_937_ = l_Lean_Syntax_isOfKind(v_stx_926_, v___x_936_);
v___x_938_ = lean_box(v___x_937_);
v___y_939_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed), 11, 2);
lean_closure_set(v___y_939_, 0, v___x_938_);
lean_closure_set(v___y_939_, 1, v_stx_926_);
v___x_940_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(v___y_939_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed(lean_object* v_stx_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(v_stx_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1(){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_957_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_958_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1));
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1));
v___x_960_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed), 10, 0);
v___x_961_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_957_, v___x_958_, v___x_959_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___boxed(lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
return v_res_963_;
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
