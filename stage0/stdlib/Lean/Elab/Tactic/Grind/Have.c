// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Have
// Imports: public import Lean.Elab.Tactic.Grind.Basic import Init.Grind.Interactive import Lean.Meta.Tactic.Assert import Lean.Meta.Tactic.Grind.Intro import Lean.Meta.Tactic.Grind.SearchM import Lean.Elab.SyntheticMVars
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__19;
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__16;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__15;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__15;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7;
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__7;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
lean_object* l_Lean_Elab_Tactic_Grind_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2;
lean_object* l_Lean_Meta_Grind_withCheapCasesOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__17;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__2;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2;
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__18;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__12;
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10;
lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__5;
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__0;
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(uint8_t, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__14;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(x_1, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_14 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_13, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Elab_Term_PostponeBehavior_ofBool(x_3);
x_18 = 0;
lean_inc(x_9);
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(x_15, x_9, x_20);
lean_dec(x_9);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse stopped: guard failed at ", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_36; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_18 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_5, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 5);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 3);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 4);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 5);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 6);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 7);
x_27 = lean_ctor_get(x_5, 6);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 x_31 = x_5;
} else {
 lean_dec_ref(x_5);
 x_31 = lean_box(0);
}
if (lean_obj_tag(x_27) == 0)
{
x_32 = x_27;
goto block_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_box(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_42, 0, x_41);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec_ref(x_42);
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(x_1, x_46);
x_36 = x_47;
goto block_38;
}
else
{
if (x_1 == 0)
{
lean_dec_ref(x_42);
goto block_45;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3;
x_50 = 0;
x_51 = l_Lean_KVMap_getBool(x_12, x_49, x_50);
if (x_51 == 0)
{
lean_dec_ref(x_42);
goto block_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_42);
x_54 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4;
x_55 = lean_box(0);
lean_inc(x_52);
x_56 = l_Lean_Syntax_formatStx(x_52, x_55, x_50);
x_57 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__5;
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_format_pretty(x_56, x_57, x_58, x_58);
x_60 = lean_string_append(x_54, x_59);
lean_dec_ref(x_59);
x_61 = lean_dbg_trace(x_60, x_53);
x_62 = lean_unbox(x_61);
x_36 = x_62;
goto block_38;
}
}
}
block_45:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(x_1, x_43);
x_36 = x_44;
goto block_38;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 7, 11);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_18);
lean_ctor_set(x_33, 3, x_19);
lean_ctor_set(x_33, 4, x_20);
lean_ctor_set(x_33, 5, x_21);
lean_ctor_set(x_33, 6, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*7, x_15);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 1, x_16);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 2, x_17);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 3, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 4, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 5, x_24);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 6, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 7, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 8, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 9, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 10, x_30);
x_34 = lean_apply_9(x_2, x_3, x_4, x_33, x_6, x_7, x_8, x_9, x_10, x_11);
return x_34;
}
block_38:
{
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_27);
x_37 = lean_box(0);
x_32 = x_37;
goto block_35;
}
else
{
x_32 = x_27;
goto block_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_17 = l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withMainContext), 11, 2);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_16);
x_19 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_dec(x_1);
lean_ctor_set(x_10, 5, x_19);
x_20 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_17, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_withMainContext), 11, 2);
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
x_43 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_39, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_42, x_11, x_12);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___lam__0), 9, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg(x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_mk_ref(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_15 = l_Lean_Meta_Grind_intros(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_getGoal___redArg(x_13, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_11, 1, x_22);
lean_ctor_set(x_11, 0, x_18);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_11);
lean_dec(x_13);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_11);
lean_dec(x_13);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
lean_inc(x_34);
x_36 = l_Lean_Meta_Grind_intros(x_2, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = l_Lean_Meta_Grind_getGoal___redArg(x_34, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_st_ref_get(x_34, x_40);
lean_dec(x_34);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_34);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
x_51 = lean_ctor_get(x_36, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_36, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_53 = x_36;
} else {
 lean_dec_ref(x_36);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_mk_empty_array_with_capacity(x_1);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0), 10, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
x_17 = l_Lean_MVarId_withContext___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(x_3, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letDecl", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__7;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__12;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value has metavariables", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type has metavariables", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elaborated term is not a `have` declaration", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_2, x_16);
x_18 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__0;
x_19 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__1;
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
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg(x_14);
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
x_30 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__2;
x_31 = l_Lean_Name_mkStr4(x_3, x_4, x_18, x_30);
x_32 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__4;
x_33 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__5;
lean_inc(x_27);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_27);
x_35 = l_Lean_Syntax_node1(x_27, x_31, x_34);
x_36 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__6;
lean_inc(x_27);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__8;
x_39 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9;
lean_inc(x_25);
lean_inc(x_24);
x_40 = l_Lean_addMacroScope(x_24, x_39, x_25);
x_41 = lean_box(0);
x_42 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__13;
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
lean_inc(x_7);
lean_inc_ref(x_6);
x_46 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(x_44, x_45, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 8)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_51);
lean_dec_ref(x_47);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Expr_hasMVar(x_50);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_hasMVar(x_51);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(x_7, x_10, x_11, x_12, x_13, x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_ctor_get(x_56, 2);
x_62 = lean_ctor_get(x_56, 3);
x_63 = lean_ctor_get(x_56, 4);
x_64 = lean_ctor_get(x_56, 5);
x_65 = lean_ctor_get(x_56, 6);
x_66 = lean_ctor_get(x_56, 7);
x_67 = lean_ctor_get(x_56, 8);
x_68 = lean_ctor_get(x_56, 9);
x_69 = lean_ctor_get(x_56, 10);
x_70 = lean_ctor_get(x_56, 11);
x_71 = lean_ctor_get(x_56, 12);
x_72 = lean_ctor_get(x_56, 13);
x_73 = lean_ctor_get(x_56, 14);
x_74 = lean_ctor_get(x_56, 15);
x_75 = lean_ctor_get(x_56, 16);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_76 = l_Lean_MVarId_assert(x_59, x_49, x_50, x_51, x_10, x_11, x_12, x_13, x_57);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
lean_inc(x_77);
lean_ctor_set(x_56, 0, x_77);
x_79 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__1), 11, 3);
lean_closure_set(x_79, 0, x_52);
lean_closure_set(x_79, 1, x_56);
lean_closure_set(x_79, 2, x_77);
x_80 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_withCheapCasesOnly), 10, 2);
lean_closure_set(x_80, 0, lean_box(0));
lean_closure_set(x_80, 1, x_79);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_81 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_80, x_6, x_7, x_10, x_11, x_12, x_13, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_dec(x_85);
lean_ctor_set_tag(x_82, 1);
lean_ctor_set(x_82, 1, x_41);
x_86 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_82, x_7, x_10, x_11, x_12, x_13, x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 0);
lean_inc(x_87);
lean_dec(x_82);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_41);
x_89 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_88, x_7, x_10, x_11, x_12, x_13, x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
x_90 = !lean_is_exclusive(x_81);
if (x_90 == 0)
{
return x_81;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_81, 0);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_81);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_free_object(x_56);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
x_94 = !lean_is_exclusive(x_76);
if (x_94 == 0)
{
return x_76;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_76, 0);
x_96 = lean_ctor_get(x_76, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_76);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_56, 0);
x_99 = lean_ctor_get(x_56, 1);
x_100 = lean_ctor_get(x_56, 2);
x_101 = lean_ctor_get(x_56, 3);
x_102 = lean_ctor_get(x_56, 4);
x_103 = lean_ctor_get(x_56, 5);
x_104 = lean_ctor_get(x_56, 6);
x_105 = lean_ctor_get(x_56, 7);
x_106 = lean_ctor_get_uint8(x_56, sizeof(void*)*17);
x_107 = lean_ctor_get(x_56, 8);
x_108 = lean_ctor_get(x_56, 9);
x_109 = lean_ctor_get(x_56, 10);
x_110 = lean_ctor_get(x_56, 11);
x_111 = lean_ctor_get(x_56, 12);
x_112 = lean_ctor_get(x_56, 13);
x_113 = lean_ctor_get(x_56, 14);
x_114 = lean_ctor_get(x_56, 15);
x_115 = lean_ctor_get(x_56, 16);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_56);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_116 = l_Lean_MVarId_assert(x_98, x_49, x_50, x_51, x_10, x_11, x_12, x_13, x_57);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
lean_inc(x_117);
x_119 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_99);
lean_ctor_set(x_119, 2, x_100);
lean_ctor_set(x_119, 3, x_101);
lean_ctor_set(x_119, 4, x_102);
lean_ctor_set(x_119, 5, x_103);
lean_ctor_set(x_119, 6, x_104);
lean_ctor_set(x_119, 7, x_105);
lean_ctor_set(x_119, 8, x_107);
lean_ctor_set(x_119, 9, x_108);
lean_ctor_set(x_119, 10, x_109);
lean_ctor_set(x_119, 11, x_110);
lean_ctor_set(x_119, 12, x_111);
lean_ctor_set(x_119, 13, x_112);
lean_ctor_set(x_119, 14, x_113);
lean_ctor_set(x_119, 15, x_114);
lean_ctor_set(x_119, 16, x_115);
lean_ctor_set_uint8(x_119, sizeof(void*)*17, x_106);
x_120 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__1), 11, 3);
lean_closure_set(x_120, 0, x_52);
lean_closure_set(x_120, 1, x_119);
lean_closure_set(x_120, 2, x_117);
x_121 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_withCheapCasesOnly), 10, 2);
lean_closure_set(x_121, 0, lean_box(0));
lean_closure_set(x_121, 1, x_120);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_122 = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(x_121, x_6, x_7, x_10, x_11, x_12, x_13, x_118);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
 lean_ctor_set_tag(x_127, 1);
}
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_41);
x_128 = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(x_127, x_7, x_10, x_11, x_12, x_13, x_124);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
x_129 = lean_ctor_get(x_122, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_122, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_131 = x_122;
} else {
 lean_dec_ref(x_122);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_115);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_116, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_135 = x_116;
} else {
 lean_dec_ref(x_116);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
x_137 = !lean_is_exclusive(x_55);
if (x_137 == 0)
{
return x_55;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_55, 0);
x_139 = lean_ctor_get(x_55, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_55);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
x_141 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__15;
x_142 = l_Lean_indentExpr(x_51);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg(x_143, x_10, x_11, x_12, x_13, x_48);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_51);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
x_145 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__17;
x_146 = l_Lean_indentExpr(x_50);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg(x_147, x_10, x_11, x_12, x_13, x_48);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_7);
lean_dec_ref(x_6);
x_149 = lean_ctor_get(x_46, 1);
lean_inc(x_149);
lean_dec_ref(x_46);
x_150 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__19;
x_151 = l_Lean_indentExpr(x_47);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg(x_152, x_10, x_11, x_12, x_13, x_149);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
return x_153;
}
}
else
{
uint8_t x_154; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
x_154 = !lean_is_exclusive(x_46);
if (x_154 == 0)
{
return x_46;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_46, 0);
x_156 = lean_ctor_get(x_46, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_46);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___boxed), 14, 5);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_12);
lean_closure_set(x_17, 4, x_13);
x_18 = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
x_16 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Have", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalHave", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14;
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0;
x_3 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5;
x_4 = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__15;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_SearchM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Have(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Interactive(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SearchM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0);
l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1);
l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2);
l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3);
l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4);
l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__5 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__5);
l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_____private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__1);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__0 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__0);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__1);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__2);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__3);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__4 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__4);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__5);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__6 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__6);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__7);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__8 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__8);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__9);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__10 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__10);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__11 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__11);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__12 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__12);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__13 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__13);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__14 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__14);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__15 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__15);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__16 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__16);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__17 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__17);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__18 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__18);
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__19 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__2___closed__19);
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
l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__15 = _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__15);
if (builtin) {res = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
