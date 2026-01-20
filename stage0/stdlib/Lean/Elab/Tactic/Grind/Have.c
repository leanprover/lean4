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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_Grind_setGoals___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getGoals___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9;
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16;
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5;
lean_object* l_Lean_Elab_Tactic_Grind_throwNoGoalsToBeSolved___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2;
lean_object* l_Lean_Elab_Tactic_Grind_liftAction___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2;
lean_object* l_Lean_Meta_Grind_Action_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0;
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Meta_Grind_mkResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5;
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___boxed(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1;
lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1;
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1;
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15;
lean_object* l_Lean_Meta_Grind_markGrindName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(uint8_t, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
lean_object* l_Lean_Meta_Grind_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(x_1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_14 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_13, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Elab_Term_PostponeBehavior_ofBool(x_3);
x_17 = 0;
lean_inc(x_9);
x_18 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec_ref(x_18);
x_19 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(x_15, x_9);
lean_dec(x_9);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse stopped: guard failed at ", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_36; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_17 = lean_ctor_get(x_5, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_5, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 5);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 3);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 4);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 5);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 6);
x_26 = lean_ctor_get(x_5, 6);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 7);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 8);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 9);
x_30 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 x_31 = x_5;
} else {
 lean_dec_ref(x_5);
 x_31 = lean_box(0);
}
if (lean_obj_tag(x_26) == 0)
{
x_32 = x_26;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_box(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_42, 0, x_41);
if (lean_obj_tag(x_40) == 1)
{
if (x_1 == 0)
{
lean_dec_ref(x_42);
goto block_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_12, 0);
x_48 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3;
x_49 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_47, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_dec_ref(x_42);
goto block_45;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
if (lean_obj_tag(x_50) == 1)
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_50, 0);
lean_dec_ref(x_50);
if (x_51 == 0)
{
lean_dec_ref(x_42);
goto block_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_42);
x_54 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4;
x_55 = lean_box(0);
x_56 = 0;
lean_inc(x_52);
x_57 = l_Lean_Syntax_formatStx(x_52, x_55, x_56);
x_58 = l_Std_Format_defWidth;
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Std_Format_pretty(x_57, x_58, x_59, x_59);
x_61 = lean_string_append(x_54, x_60);
lean_dec_ref(x_60);
x_62 = lean_dbg_trace(x_61, x_53);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
x_36 = x_63;
goto block_38;
}
}
else
{
lean_dec(x_50);
lean_dec_ref(x_42);
goto block_45;
}
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec_ref(x_42);
x_64 = lean_box(0);
x_65 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(x_1, x_64);
x_36 = x_65;
goto block_38;
}
block_45:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(x_1, x_43);
x_36 = x_44;
goto block_38;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 8, 10);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_17);
lean_ctor_set(x_33, 3, x_18);
lean_ctor_set(x_33, 4, x_19);
lean_ctor_set(x_33, 5, x_20);
lean_ctor_set(x_33, 6, x_32);
lean_ctor_set(x_33, 7, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_15);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 1, x_16);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 2, x_21);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 3, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 4, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 5, x_24);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 6, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 7, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 8, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 9, x_29);
x_34 = lean_apply_9(x_2, x_3, x_4, x_33, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_34;
}
block_38:
{
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_box(0);
x_32 = x_37;
goto block_35;
}
else
{
x_32 = x_26;
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed), 12, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
x_17 = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_10, 5);
x_15 = lean_box(x_3);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed), 12, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
x_17 = 1;
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withMainContext___boxed), 11, 2);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_dec(x_1);
lean_ctor_set(x_10, 5, x_19);
x_20 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
x_24 = lean_ctor_get(x_10, 3);
x_25 = lean_ctor_get(x_10, 4);
x_26 = lean_ctor_get(x_10, 5);
x_27 = lean_ctor_get(x_10, 6);
x_28 = lean_ctor_get(x_10, 7);
x_29 = lean_ctor_get(x_10, 8);
x_30 = lean_ctor_get(x_10, 9);
x_31 = lean_ctor_get(x_10, 10);
x_32 = lean_ctor_get(x_10, 11);
x_33 = lean_ctor_get_uint8(x_10, sizeof(void*)*14);
x_34 = lean_ctor_get(x_10, 12);
x_35 = lean_ctor_get_uint8(x_10, sizeof(void*)*14 + 1);
x_36 = lean_ctor_get(x_10, 13);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_37 = lean_box(x_3);
lean_inc(x_1);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed), 12, 3);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_2);
lean_closure_set(x_38, 2, x_37);
x_39 = 1;
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withMainContext___boxed), 11, 2);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, x_38);
x_41 = l_Lean_replaceRef(x_1, x_26);
lean_dec(x_26);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_42, 0, x_21);
lean_ctor_set(x_42, 1, x_22);
lean_ctor_set(x_42, 2, x_23);
lean_ctor_set(x_42, 3, x_24);
lean_ctor_set(x_42, 4, x_25);
lean_ctor_set(x_42, 5, x_41);
lean_ctor_set(x_42, 6, x_27);
lean_ctor_set(x_42, 7, x_28);
lean_ctor_set(x_42, 8, x_29);
lean_ctor_set(x_42, 9, x_30);
lean_ctor_set(x_42, 10, x_31);
lean_ctor_set(x_42, 11, x_32);
lean_ctor_set(x_42, 12, x_34);
lean_ctor_set(x_42, 13, x_36);
lean_ctor_set_uint8(x_42, sizeof(void*)*14, x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*14 + 1, x_35);
x_43 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_39, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_42, x_11);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letDecl", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7;
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Action_intros___boxed), 13, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value has metavariables", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type has metavariables", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elaborated term is not a `have` declaration", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_1 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_2, x_16);
x_18 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0;
x_19 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1;
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_20 = l_Lean_Name_mkStr4(x_3, x_4, x_18, x_19);
lean_inc(x_17);
x_21 = l_Lean_Syntax_isOfKind(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_23 = lean_ctor_get(x_12, 5);
x_24 = lean_ctor_get(x_12, 10);
x_25 = lean_ctor_get(x_12, 11);
x_26 = 0;
x_27 = l_Lean_SourceInfo_fromRef(x_23, x_26);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_28 = l_Lean_Name_mkStr4(x_3, x_4, x_18, x_5);
lean_inc(x_27);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_5);
x_30 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2;
x_31 = l_Lean_Name_mkStr4(x_3, x_4, x_18, x_30);
x_32 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4;
x_33 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5;
lean_inc(x_27);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_27);
x_35 = l_Lean_Syntax_node1(x_27, x_31, x_34);
x_36 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6;
lean_inc(x_27);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8;
x_39 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9;
lean_inc(x_25);
lean_inc(x_24);
x_40 = l_Lean_addMacroScope(x_24, x_39, x_25);
x_41 = lean_box(0);
x_42 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13;
lean_inc(x_27);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
x_44 = l_Lean_Syntax_node5(x_27, x_28, x_29, x_35, x_17, x_37, x_43);
x_45 = lean_box(0);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_46 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(x_44, x_45, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
if (lean_obj_tag(x_47) == 8)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_103; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_50);
lean_dec_ref(x_47);
x_103 = l_Lean_Expr_hasMVar(x_49);
if (x_103 == 0)
{
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
x_91 = x_9;
x_92 = x_10;
x_93 = x_11;
x_94 = x_12;
x_95 = x_13;
x_96 = lean_box(0);
goto block_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_50);
lean_dec(x_48);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_104 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18;
x_105 = l_Lean_indentExpr(x_49);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_106, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_107;
}
block_87:
{
lean_object* x_58; 
x_58 = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(x_52, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
x_63 = l_Lean_MVarId_assert(x_62, x_48, x_49, x_50, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
lean_ctor_set(x_59, 1, x_64);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_41);
x_66 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_65, x_52, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_66);
x_67 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14;
x_68 = l_Lean_Elab_Tactic_Grind_liftAction___redArg(x_67, x_51, x_52, x_53, x_54, x_55, x_56);
lean_dec(x_52);
return x_68;
}
else
{
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
return x_66;
}
}
else
{
uint8_t x_69; 
lean_free_object(x_59);
lean_dec_ref(x_61);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_59, 0);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_59);
lean_inc(x_56);
lean_inc_ref(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
x_74 = l_Lean_MVarId_assert(x_73, x_48, x_49, x_50, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_41);
x_78 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_77, x_52, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_78);
x_79 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14;
x_80 = l_Lean_Elab_Tactic_Grind_liftAction___redArg(x_79, x_51, x_52, x_53, x_54, x_55, x_56);
lean_dec(x_52);
return x_80;
}
else
{
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
return x_78;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_72);
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
x_81 = lean_ctor_get(x_74, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_82 = x_74;
} else {
 lean_dec_ref(x_74);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_56);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec(x_48);
x_84 = !lean_is_exclusive(x_58);
if (x_84 == 0)
{
return x_58;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_58, 0);
lean_inc(x_85);
lean_dec(x_58);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
block_102:
{
uint8_t x_97; 
lean_dec(x_91);
lean_dec_ref(x_90);
x_97 = l_Lean_Expr_hasMVar(x_50);
if (x_97 == 0)
{
x_51 = x_88;
x_52 = x_89;
x_53 = x_92;
x_54 = x_93;
x_55 = x_94;
x_56 = x_95;
x_57 = lean_box(0);
goto block_87;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec_ref(x_49);
lean_dec(x_48);
x_98 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16;
x_99 = l_Lean_indentExpr(x_50);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_100, x_92, x_93, x_94, x_95);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_92);
return x_101;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_108 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20;
x_109 = l_Lean_indentExpr(x_47);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_110, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_112 = !lean_is_exclusive(x_46);
if (x_112 == 0)
{
return x_46;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_46, 0);
lean_inc(x_113);
lean_dec(x_46);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
x_16 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("have", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
x_3 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1;
x_5 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
x_12 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1;
x_13 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4;
x_14 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed), 14, 5);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_12);
lean_closure_set(x_17, 4, x_13);
x_18 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Have", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalHave", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5;
x_4 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`finish` failed\n", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("this", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_13 = lean_unsigned_to_nat(0u);
x_192 = lean_unsigned_to_nat(1u);
x_193 = l_Lean_Syntax_getArg(x_2, x_192);
x_194 = l_Lean_Syntax_isNone(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_inc(x_193);
x_195 = l_Lean_Syntax_matchesNull(x_193, x_192);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_193);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_196 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = l_Lean_Syntax_getArg(x_193, x_13);
lean_dec(x_193);
x_198 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5;
lean_inc(x_197);
x_199 = l_Lean_Syntax_isOfKind(x_197, x_198);
if (x_199 == 0)
{
lean_object* x_200; 
lean_dec(x_197);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_200 = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
return x_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_197);
x_176 = x_201;
x_177 = x_3;
x_178 = x_4;
x_179 = x_5;
x_180 = x_6;
x_181 = x_7;
x_182 = x_8;
x_183 = x_9;
x_184 = x_10;
x_185 = lean_box(0);
goto block_191;
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_193);
x_202 = lean_box(0);
x_176 = x_202;
x_177 = x_3;
x_178 = x_4;
x_179 = x_5;
x_180 = x_6;
x_181 = x_7;
x_182 = x_8;
x_183 = x_9;
x_184 = x_10;
x_185 = lean_box(0);
goto block_191;
}
block_39:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(x_14, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
x_29 = l_Lean_MVarId_assert(x_18, x_19, x_17, x_28, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
x_33 = l_Lean_Elab_Tactic_Grind_setGoals___redArg(x_32, x_21);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_33);
x_34 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14;
x_35 = l_Lean_Elab_Tactic_Grind_liftAction___redArg(x_34, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_21);
return x_35;
}
else
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
return x_33;
}
}
else
{
uint8_t x_36; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_16);
lean_dec_ref(x_15);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
block_161:
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_51 = lean_box(0);
x_52 = 0;
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
lean_inc(x_48);
lean_inc_ref(x_41);
x_53 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(x_49, x_51, x_52, x_41, x_48, x_42, x_45, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
lean_inc(x_54);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = 0;
x_57 = lean_box(0);
lean_inc_ref(x_40);
x_58 = l_Lean_Meta_mkFreshExprMVar(x_55, x_56, x_57, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_Elab_Tactic_Grind_getGoals___redArg(x_48);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
if (lean_obj_tag(x_61) == 1)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_61, 1);
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
x_68 = l_Lean_Expr_mvarId_x21(x_59);
lean_inc_ref(x_66);
lean_ctor_set(x_63, 1, x_68);
x_69 = lean_box(0);
lean_inc_ref(x_63);
lean_ctor_set(x_61, 1, x_69);
x_70 = l_Lean_Elab_Tactic_Grind_setGoals___redArg(x_61, x_48);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_70);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_solve___boxed), 10, 1);
lean_closure_set(x_71, 0, x_63);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
lean_inc_ref(x_41);
x_72 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_71, x_41, x_48, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
if (lean_obj_tag(x_73) == 1)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
x_74 = lean_ctor_get(x_41, 3);
lean_inc_ref(x_74);
x_75 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkResult___boxed), 11, 2);
lean_closure_set(x_75, 0, x_74);
lean_closure_set(x_75, 1, x_73);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
x_76 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_75, x_41, x_48, x_40, x_47, x_46, x_43);
lean_dec(x_48);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
x_78 = l_Lean_Meta_Grind_Result_toMessageData(x_77, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_81, x_40, x_47, x_46, x_43);
lean_dec(x_43);
lean_dec_ref(x_46);
lean_dec(x_47);
lean_dec_ref(x_40);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_40);
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
return x_78;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_40);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
return x_76;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
else
{
lean_dec(x_73);
x_14 = x_59;
x_15 = x_66;
x_16 = x_65;
x_17 = x_54;
x_18 = x_67;
x_19 = x_50;
x_20 = x_41;
x_21 = x_48;
x_22 = x_40;
x_23 = x_47;
x_24 = x_46;
x_25 = x_43;
x_26 = lean_box(0);
goto block_39;
}
}
else
{
uint8_t x_89; 
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
x_89 = !lean_is_exclusive(x_72);
if (x_89 == 0)
{
return x_72;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_72, 0);
lean_inc(x_90);
lean_dec(x_72);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
return x_70;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_61, 1);
x_93 = lean_ctor_get(x_63, 0);
x_94 = lean_ctor_get(x_63, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_63);
x_95 = l_Lean_Expr_mvarId_x21(x_59);
lean_inc_ref(x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_box(0);
lean_inc_ref(x_96);
lean_ctor_set(x_61, 1, x_97);
lean_ctor_set(x_61, 0, x_96);
x_98 = l_Lean_Elab_Tactic_Grind_setGoals___redArg(x_61, x_48);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_98);
x_99 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_solve___boxed), 10, 1);
lean_closure_set(x_99, 0, x_96);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
lean_inc_ref(x_41);
x_100 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_99, x_41, x_48, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
if (lean_obj_tag(x_101) == 1)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
x_102 = lean_ctor_get(x_41, 3);
lean_inc_ref(x_102);
x_103 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkResult___boxed), 11, 2);
lean_closure_set(x_103, 0, x_102);
lean_closure_set(x_103, 1, x_101);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
x_104 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_103, x_41, x_48, x_40, x_47, x_46, x_43);
lean_dec(x_48);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
x_106 = l_Lean_Meta_Grind_Result_toMessageData(x_105, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_109, x_40, x_47, x_46, x_43);
lean_dec(x_43);
lean_dec_ref(x_46);
lean_dec(x_47);
lean_dec_ref(x_40);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_40);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_40);
x_114 = lean_ctor_get(x_104, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_115 = x_104;
} else {
 lean_dec_ref(x_104);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_dec(x_101);
x_14 = x_59;
x_15 = x_93;
x_16 = x_92;
x_17 = x_54;
x_18 = x_94;
x_19 = x_50;
x_20 = x_41;
x_21 = x_48;
x_22 = x_40;
x_23 = x_47;
x_24 = x_46;
x_25 = x_43;
x_26 = lean_box(0);
goto block_39;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
x_117 = lean_ctor_get(x_100, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_118 = x_100;
} else {
 lean_dec_ref(x_100);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_dec_ref(x_96);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
return x_98;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_120 = lean_ctor_get(x_61, 0);
x_121 = lean_ctor_get(x_61, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_61);
x_122 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Expr_mvarId_x21(x_59);
lean_inc_ref(x_122);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_box(0);
lean_inc_ref(x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_Tactic_Grind_setGoals___redArg(x_128, x_48);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_129);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_solve___boxed), 10, 1);
lean_closure_set(x_130, 0, x_126);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
lean_inc_ref(x_41);
x_131 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_130, x_41, x_48, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
x_133 = lean_ctor_get(x_41, 3);
lean_inc_ref(x_133);
x_134 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkResult___boxed), 11, 2);
lean_closure_set(x_134, 0, x_133);
lean_closure_set(x_134, 1, x_132);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
x_135 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_134, x_41, x_48, x_40, x_47, x_46, x_43);
lean_dec(x_48);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
lean_inc(x_43);
lean_inc_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_40);
x_137 = l_Lean_Meta_Grind_Result_toMessageData(x_136, x_40, x_47, x_46, x_43);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1;
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_140, x_40, x_47, x_46, x_43);
lean_dec(x_43);
lean_dec_ref(x_46);
lean_dec(x_47);
lean_dec_ref(x_40);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_40);
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_143 = x_137;
} else {
 lean_dec_ref(x_137);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_40);
x_145 = lean_ctor_get(x_135, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_146 = x_135;
} else {
 lean_dec_ref(x_135);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
return x_147;
}
}
else
{
lean_dec(x_132);
x_14 = x_59;
x_15 = x_122;
x_16 = x_121;
x_17 = x_54;
x_18 = x_123;
x_19 = x_50;
x_20 = x_41;
x_21 = x_48;
x_22 = x_40;
x_23 = x_47;
x_24 = x_46;
x_25 = x_43;
x_26 = lean_box(0);
goto block_39;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
x_148 = lean_ctor_get(x_131, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_149 = x_131;
} else {
 lean_dec_ref(x_131);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_dec_ref(x_126);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
return x_129;
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec_ref(x_41);
x_151 = l_Lean_Elab_Tactic_Grind_throwNoGoalsToBeSolved___redArg(x_40, x_47, x_46, x_43);
lean_dec(x_43);
lean_dec_ref(x_46);
lean_dec(x_47);
lean_dec_ref(x_40);
return x_151;
}
}
else
{
uint8_t x_152; 
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
x_152 = !lean_is_exclusive(x_60);
if (x_152 == 0)
{
return x_60;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_60, 0);
lean_inc(x_153);
lean_dec(x_60);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
x_155 = !lean_is_exclusive(x_58);
if (x_155 == 0)
{
return x_58;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_58, 0);
lean_inc(x_156);
lean_dec(x_58);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
x_158 = !lean_is_exclusive(x_53);
if (x_158 == 0)
{
return x_53;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_53, 0);
lean_inc(x_159);
lean_dec(x_53);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
block_175:
{
uint8_t x_173; 
x_173 = l_Lean_Name_hasMacroScopes(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = l_Lean_Meta_Grind_markGrindName(x_172);
x_40 = x_163;
x_41 = x_162;
x_42 = x_164;
x_43 = x_165;
x_44 = lean_box(0);
x_45 = x_166;
x_46 = x_168;
x_47 = x_169;
x_48 = x_170;
x_49 = x_171;
x_50 = x_174;
goto block_161;
}
else
{
x_40 = x_163;
x_41 = x_162;
x_42 = x_164;
x_43 = x_165;
x_44 = lean_box(0);
x_45 = x_166;
x_46 = x_168;
x_47 = x_169;
x_48 = x_170;
x_49 = x_171;
x_50 = x_172;
goto block_161;
}
}
block_191:
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_unsigned_to_nat(3u);
x_187 = l_Lean_Syntax_getArg(x_2, x_186);
if (lean_obj_tag(x_176) == 1)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_176, 0);
lean_inc(x_188);
lean_dec_ref(x_176);
x_189 = l_Lean_TSyntax_getId(x_188);
lean_dec(x_188);
x_162 = x_177;
x_163 = x_181;
x_164 = x_179;
x_165 = x_184;
x_166 = x_180;
x_167 = lean_box(0);
x_168 = x_183;
x_169 = x_182;
x_170 = x_178;
x_171 = x_187;
x_172 = x_189;
goto block_175;
}
else
{
lean_object* x_190; 
lean_dec(x_176);
x_190 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3;
x_162 = x_177;
x_163 = x_181;
x_164 = x_179;
x_165 = x_184;
x_166 = x_180;
x_167 = lean_box(0);
x_168 = x_183;
x_169 = x_182;
x_170 = x_178;
x_171 = x_187;
x_172 = x_190;
goto block_175;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("haveSilent", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
x_3 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1;
x_5 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
x_13 = lean_box(x_12);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed), 11, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_1);
x_15 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalHaveSilent", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
x_3 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1;
x_4 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
return x_2;
}
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
l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0);
l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1);
l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2);
l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3);
l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4);
l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
