// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrite
// Imports: Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Replace Lean.Elab.Tactic.Location Lean.Elab.Tactic.Config
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__6;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__1;
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__5;
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__5;
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4;
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__4;
static lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__7;
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__1;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabRewriteConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__8;
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__6;
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__8;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___closed__1;
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__1;
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__5;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__3;
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabRewriteConfig___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__2;
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__2;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__1;
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__3;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__3;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__1;
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___closed__3;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortTacticExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_getMainTarget(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_MVarId_rewrite(x_15, x_18, x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = l_Lean_MVarId_replaceTargetEq(x_24, x_26, x_27, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_21, 2);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_replaceMainGoal(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_14);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_hasSyntheticSorry(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Tactic_rewriteTarget___lambda__1(x_16, x_3, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg(x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_box(0);
x_14 = lean_box(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lambda__2___boxed), 13, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_3);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_5);
x_17 = 1;
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_rewriteTarget___lambda__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic_rewriteTarget___lambda__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_rewriteTarget(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_10);
x_15 = l_Lean_FVarId_getDecl(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
x_22 = l_Lean_MVarId_rewrite(x_19, x_21, x_2, x_3, x_4, x_10, x_11, x_12, x_13, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_hasSyntheticSorry(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1(x_3, x_17, x_4, x_5, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_22 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg(x_18);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
x_13 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_18, x_2, x_20, x_21, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_15, 2);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_replaceMainGoal(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(0);
x_15 = lean_box(x_2);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2___boxed), 14, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_4);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__3), 11, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_3);
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to rewrite using equation theorems for '", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'.", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_root_", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_16 = l_Lean_MessageData_ofName(x_4);
x_17 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
x_22 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_dec(x_6);
x_27 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__8;
x_28 = l_Lean_Name_append(x_27, x_25);
x_29 = 0;
x_30 = l_Lean_mkIdentFrom(x_3, x_28, x_29);
x_31 = lean_box(x_2);
lean_inc(x_1);
x_32 = lean_apply_2(x_1, x_31, x_30);
x_33 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = l_Lean_Exception_isInterrupt(x_38);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Exception_isRuntime(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_36);
lean_dec(x_38);
x_42 = l_Lean_Elab_Tactic_SavedState_restore(x_34, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_39);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_6 = x_26;
x_15 = x_43;
goto _start;
}
else
{
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_36;
}
}
else
{
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_36;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_36, 0);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_36);
x_47 = l_Lean_Exception_isInterrupt(x_45);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Exception_isRuntime(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
x_49 = l_Lean_Elab_Tactic_SavedState_restore(x_34, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_6 = x_26;
x_15 = x_50;
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_34);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getFVarId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" Try rewriting with '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_15 = l_Lean_Meta_getEqnsFor_x3f(x_5, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(x_2);
x_19 = lean_apply_11(x_1, x_18, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
x_26 = lean_array_to_list(x_22);
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_5);
x_28 = l_Lean_Name_str___override(x_5, x_27);
x_29 = l_Lean_MessageData_ofName(x_28);
x_30 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_34 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_4, x_5, x_33, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_5, x_10, x_11, x_12, x_13, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_10, 2);
lean_inc(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_16, 0, x_39);
x_41 = lean_box(0);
x_42 = 0;
x_43 = l_Lean_Elab_Term_addTermInfo(x_4, x_37, x_40, x_16, x_41, x_42, x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_36;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_36, 0);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_36);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_34);
if (x_58 == 0)
{
return x_34;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_34, 0);
x_60 = lean_ctor_get(x_34, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_34);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_63 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_4, x_5, x_62, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_5, x_10, x_11, x_12, x_13, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_10, 2);
lean_inc(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_16, 0, x_68);
x_70 = lean_box(0);
x_71 = 0;
x_72 = l_Lean_Elab_Term_addTermInfo(x_4, x_66, x_69, x_16, x_70, x_71, x_71, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_72);
if (x_79 == 0)
{
return x_72;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_72, 0);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_72);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_65);
if (x_83 == 0)
{
return x_65;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_65, 0);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_65);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_63);
if (x_87 == 0)
{
return x_63;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_63, 0);
x_89 = lean_ctor_get(x_63, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_63);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_16, 0);
lean_inc(x_91);
lean_dec(x_16);
x_92 = lean_array_get_size(x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_dec_eq(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_to_list(x_91);
if (x_94 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_5);
x_97 = l_Lean_Name_str___override(x_5, x_96);
x_98 = l_Lean_MessageData_ofName(x_97);
x_99 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_103 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_4, x_5, x_102, x_95, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_5, x_10, x_11, x_12, x_13, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_10, 2);
lean_inc(x_108);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_108);
x_111 = lean_box(0);
x_112 = 0;
x_113 = l_Lean_Elab_Term_addTermInfo(x_4, x_106, x_109, x_110, x_111, x_112, x_112, x_8, x_9, x_10, x_11, x_12, x_13, x_107);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = lean_box(0);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_122 = lean_ctor_get(x_105, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_105, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_124 = x_105;
} else {
 lean_dec_ref(x_105);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_126 = lean_ctor_get(x_103, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_103, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_128 = x_103;
} else {
 lean_dec_ref(x_103);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_131 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_4, x_5, x_130, x_95, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_5, x_10, x_11, x_12, x_13, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_10, 2);
lean_inc(x_136);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_136);
x_139 = lean_box(0);
x_140 = 0;
x_141 = l_Lean_Elab_Term_addTermInfo(x_4, x_134, x_137, x_138, x_139, x_140, x_140, x_8, x_9, x_10, x_11, x_12, x_13, x_135);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_box(0);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_141, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_141, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_148 = x_141;
} else {
 lean_dec_ref(x_141);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_150 = lean_ctor_get(x_133, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_133, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_152 = x_133;
} else {
 lean_dec_ref(x_133);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_154 = lean_ctor_get(x_131, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_131, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_156 = x_131;
} else {
 lean_dec_ref(x_131);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_15);
if (x_158 == 0)
{
return x_15;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_15, 0);
x_160 = lean_ctor_get(x_15, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_15);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_14 = l_Lean_Meta_getEqnsFor_x3f(x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(x_2);
x_18 = lean_apply_11(x_1, x_17, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
x_25 = lean_array_to_list(x_21);
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_4);
x_27 = l_Lean_Name_str___override(x_4, x_26);
x_28 = l_Lean_MessageData_ofName(x_27);
x_29 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_33 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_3, x_4, x_32, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_4, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_9, 2);
lean_inc(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_15, 0, x_38);
x_40 = lean_box(0);
x_41 = 0;
x_42 = l_Lean_Elab_Term_addTermInfo(x_3, x_36, x_39, x_15, x_40, x_41, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
return x_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_35, 0);
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_35);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_33);
if (x_57 == 0)
{
return x_33;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_33, 0);
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_33);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_62 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_3, x_4, x_61, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_4, x_9, x_10, x_11, x_12, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_9, 2);
lean_inc(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_15, 0, x_67);
x_69 = lean_box(0);
x_70 = 0;
x_71 = l_Lean_Elab_Term_addTermInfo(x_3, x_65, x_68, x_15, x_69, x_70, x_70, x_7, x_8, x_9, x_10, x_11, x_12, x_66);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_71, 0);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_71);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_64);
if (x_82 == 0)
{
return x_64;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_64, 0);
x_84 = lean_ctor_get(x_64, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_64);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_62);
if (x_86 == 0)
{
return x_62;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_62, 0);
x_88 = lean_ctor_get(x_62, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_62);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_15, 0);
lean_inc(x_90);
lean_dec(x_15);
x_91 = lean_array_get_size(x_90);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_dec_eq(x_91, x_92);
lean_dec(x_91);
x_94 = lean_array_to_list(x_90);
if (x_93 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_4);
x_96 = l_Lean_Name_str___override(x_4, x_95);
x_97 = l_Lean_MessageData_ofName(x_96);
x_98 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_102 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_3, x_4, x_101, x_94, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_4, x_9, x_10, x_11, x_12, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_9, 2);
lean_inc(x_107);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_box(0);
x_111 = 0;
x_112 = l_Lean_Elab_Term_addTermInfo(x_3, x_105, x_108, x_109, x_110, x_111, x_111, x_7, x_8, x_9, x_10, x_11, x_12, x_106);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_121 = lean_ctor_get(x_104, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_104, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_123 = x_104;
} else {
 lean_dec_ref(x_104);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_125 = lean_ctor_get(x_102, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_102, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_127 = x_102;
} else {
 lean_dec_ref(x_102);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_130 = l_Lean_Elab_Tactic_withRWRulesSeq_go(x_1, x_2, x_3, x_4, x_129, x_94, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_4, x_9, x_10, x_11, x_12, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_9, 2);
lean_inc(x_135);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_135);
x_138 = lean_box(0);
x_139 = 0;
x_140 = l_Lean_Elab_Term_addTermInfo(x_3, x_133, x_136, x_137, x_138, x_139, x_139, x_7, x_8, x_9, x_10, x_11, x_12, x_134);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = lean_box(0);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_140, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_147 = x_140;
} else {
 lean_dec_ref(x_140);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_149 = lean_ctor_get(x_132, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_132, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_151 = x_132;
} else {
 lean_dec_ref(x_132);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_153 = lean_ctor_get(x_130, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_130, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_155 = x_130;
} else {
 lean_dec_ref(x_130);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_14);
if (x_157 == 0)
{
return x_14;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_14, 0);
x_159 = lean_ctor_get(x_14, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_14);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("explicit", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1;
x_2 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__2;
x_3 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__3;
x_4 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 5);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
lean_ctor_set(x_13, 5, x_18);
if (x_2 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__5;
lean_inc(x_3);
x_20 = l_Lean_Syntax_isOfKind(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(x_5);
x_22 = lean_apply_11(x_4, x_21, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_3, x_23);
lean_inc(x_24);
x_25 = l_Lean_Syntax_isOfKind(x_24, x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_26 = lean_box(x_5);
x_27 = lean_apply_11(x_4, x_26, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_inc(x_24);
x_28 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__1), 10, 1);
lean_closure_set(x_28, 0, x_24);
x_78 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_81 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_29 = x_82;
x_30 = x_83;
goto block_77;
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
x_87 = l_Lean_Exception_isInterrupt(x_85);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Exception_isRuntime(x_85);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_81);
lean_dec(x_85);
x_89 = 0;
x_90 = l_Lean_Elab_Tactic_SavedState_restore(x_79, x_89, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_86);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_29 = x_92;
x_30 = x_91;
goto block_77;
}
else
{
lean_dec(x_79);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_81;
}
}
else
{
lean_dec(x_79);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_81;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_81, 0);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_81);
x_95 = l_Lean_Exception_isInterrupt(x_93);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Lean_Exception_isRuntime(x_93);
if (x_96 == 0)
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_93);
x_97 = 0;
x_98 = l_Lean_Elab_Tactic_SavedState_restore(x_79, x_97, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_94);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_29 = x_100;
x_30 = x_99;
goto block_77;
}
else
{
lean_object* x_101; 
lean_dec(x_79);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_94);
return x_101;
}
}
else
{
lean_object* x_102; 
lean_dec(x_79);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_93);
lean_ctor_set(x_102, 1, x_94);
return x_102;
}
}
}
block_77:
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_24);
x_34 = l_Lean_realizeGlobalConstNoOverload(x_24, x_13, x_14, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2(x_4, x_5, x_3, x_24, x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_24);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
x_41 = l_Lean_Exception_isInterrupt(x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Exception_isRuntime(x_39);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_34);
lean_dec(x_39);
x_43 = 0;
x_44 = l_Lean_Elab_Tactic_SavedState_restore(x_32, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(x_5);
x_47 = lean_apply_11(x_4, x_46, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_45);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_34;
}
}
else
{
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_34;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_34, 0);
x_57 = lean_ctor_get(x_34, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_34);
x_58 = l_Lean_Exception_isInterrupt(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Exception_isRuntime(x_56);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_56);
x_60 = 0;
x_61 = l_Lean_Elab_Tactic_SavedState_restore(x_32, x_60, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_57);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(x_5);
x_64 = lean_apply_11(x_4, x_63, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_56);
lean_ctor_set(x_73, 1, x_57);
return x_73;
}
}
else
{
lean_object* x_74; 
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_57);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_29);
lean_dec(x_24);
x_75 = lean_box(x_5);
x_76 = lean_apply_11(x_4, x_75, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
return x_76;
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_inc(x_3);
x_103 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__1), 10, 1);
lean_closure_set(x_103, 0, x_3);
x_153 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_156 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_103, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_154);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_104 = x_157;
x_105 = x_158;
goto block_152;
}
else
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_156);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_156, 0);
x_161 = lean_ctor_get(x_156, 1);
x_162 = l_Lean_Exception_isInterrupt(x_160);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = l_Lean_Exception_isRuntime(x_160);
if (x_163 == 0)
{
uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_free_object(x_156);
lean_dec(x_160);
x_164 = 0;
x_165 = l_Lean_Elab_Tactic_SavedState_restore(x_154, x_164, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_161);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_box(0);
x_104 = x_167;
x_105 = x_166;
goto block_152;
}
else
{
lean_dec(x_154);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_156;
}
}
else
{
lean_dec(x_154);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_156;
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_156, 0);
x_169 = lean_ctor_get(x_156, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_156);
x_170 = l_Lean_Exception_isInterrupt(x_168);
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = l_Lean_Exception_isRuntime(x_168);
if (x_171 == 0)
{
uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_168);
x_172 = 0;
x_173 = l_Lean_Elab_Tactic_SavedState_restore(x_154, x_172, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_169);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_box(0);
x_104 = x_175;
x_105 = x_174;
goto block_152;
}
else
{
lean_object* x_176; 
lean_dec(x_154);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
return x_176;
}
}
else
{
lean_object* x_177; 
lean_dec(x_154);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_168);
lean_ctor_set(x_177, 1, x_169);
return x_177;
}
}
}
block_152:
{
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
x_109 = l_Lean_realizeGlobalConstNoOverload(x_3, x_13, x_14, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_107);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__3(x_4, x_5, x_3, x_110, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_111);
return x_112;
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_109, 0);
x_115 = lean_ctor_get(x_109, 1);
x_116 = l_Lean_Exception_isInterrupt(x_114);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = l_Lean_Exception_isRuntime(x_114);
if (x_117 == 0)
{
uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_free_object(x_109);
lean_dec(x_114);
x_118 = 0;
x_119 = l_Lean_Elab_Tactic_SavedState_restore(x_107, x_118, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_115);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_box(x_5);
x_122 = lean_apply_11(x_4, x_121, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_120);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
return x_122;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_122);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_122);
if (x_127 == 0)
{
return x_122;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_122, 0);
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_122);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_dec(x_107);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_109;
}
}
else
{
lean_dec(x_107);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_109;
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_109, 0);
x_132 = lean_ctor_get(x_109, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_109);
x_133 = l_Lean_Exception_isInterrupt(x_131);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = l_Lean_Exception_isRuntime(x_131);
if (x_134 == 0)
{
uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_131);
x_135 = 0;
x_136 = l_Lean_Elab_Tactic_SavedState_restore(x_107, x_135, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_132);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_box(x_5);
x_139 = lean_apply_11(x_4, x_138, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_139, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_146 = x_139;
} else {
 lean_dec_ref(x_139);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_107);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_131);
lean_ctor_set(x_148, 1, x_132);
return x_148;
}
}
else
{
lean_object* x_149; 
lean_dec(x_107);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_131);
lean_ctor_set(x_149, 1, x_132);
return x_149;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_104);
x_150 = lean_box(x_5);
x_151 = lean_apply_11(x_4, x_150, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_105);
return x_151;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; 
x_178 = lean_ctor_get(x_13, 0);
x_179 = lean_ctor_get(x_13, 1);
x_180 = lean_ctor_get(x_13, 2);
x_181 = lean_ctor_get(x_13, 3);
x_182 = lean_ctor_get(x_13, 4);
x_183 = lean_ctor_get(x_13, 5);
x_184 = lean_ctor_get(x_13, 6);
x_185 = lean_ctor_get(x_13, 7);
x_186 = lean_ctor_get(x_13, 8);
x_187 = lean_ctor_get(x_13, 9);
x_188 = lean_ctor_get(x_13, 10);
x_189 = lean_ctor_get_uint8(x_13, sizeof(void*)*12);
x_190 = lean_ctor_get(x_13, 11);
x_191 = lean_ctor_get_uint8(x_13, sizeof(void*)*12 + 1);
lean_inc(x_190);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_13);
x_192 = l_Lean_replaceRef(x_1, x_183);
lean_dec(x_183);
x_193 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_193, 0, x_178);
lean_ctor_set(x_193, 1, x_179);
lean_ctor_set(x_193, 2, x_180);
lean_ctor_set(x_193, 3, x_181);
lean_ctor_set(x_193, 4, x_182);
lean_ctor_set(x_193, 5, x_192);
lean_ctor_set(x_193, 6, x_184);
lean_ctor_set(x_193, 7, x_185);
lean_ctor_set(x_193, 8, x_186);
lean_ctor_set(x_193, 9, x_187);
lean_ctor_set(x_193, 10, x_188);
lean_ctor_set(x_193, 11, x_190);
lean_ctor_set_uint8(x_193, sizeof(void*)*12, x_189);
lean_ctor_set_uint8(x_193, sizeof(void*)*12 + 1, x_191);
if (x_2 == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__5;
lean_inc(x_3);
x_195 = l_Lean_Syntax_isOfKind(x_3, x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_box(x_5);
x_197 = lean_apply_11(x_4, x_196, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_15);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_unsigned_to_nat(1u);
x_199 = l_Lean_Syntax_getArg(x_3, x_198);
lean_inc(x_199);
x_200 = l_Lean_Syntax_isOfKind(x_199, x_6);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_199);
x_201 = lean_box(x_5);
x_202 = lean_apply_11(x_4, x_201, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_15);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_inc(x_199);
x_203 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__1), 10, 1);
lean_closure_set(x_203, 0, x_199);
x_236 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_15);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
lean_inc(x_14);
lean_inc(x_193);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_239 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_203, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_237);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_204 = x_240;
x_205 = x_241;
goto block_235;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_244 = x_239;
} else {
 lean_dec_ref(x_239);
 x_244 = lean_box(0);
}
x_245 = l_Lean_Exception_isInterrupt(x_242);
if (x_245 == 0)
{
uint8_t x_246; 
x_246 = l_Lean_Exception_isRuntime(x_242);
if (x_246 == 0)
{
uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_244);
lean_dec(x_242);
x_247 = 0;
x_248 = l_Lean_Elab_Tactic_SavedState_restore(x_237, x_247, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_243);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_box(0);
x_204 = x_250;
x_205 = x_249;
goto block_235;
}
else
{
lean_object* x_251; 
lean_dec(x_237);
lean_dec(x_199);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_244)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_244;
}
lean_ctor_set(x_251, 0, x_242);
lean_ctor_set(x_251, 1, x_243);
return x_251;
}
}
else
{
lean_object* x_252; 
lean_dec(x_237);
lean_dec(x_199);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_244)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_244;
}
lean_ctor_set(x_252, 0, x_242);
lean_ctor_set(x_252, 1, x_243);
return x_252;
}
}
block_235:
{
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_14);
lean_inc(x_193);
lean_inc(x_199);
x_209 = l_Lean_realizeGlobalConstNoOverload(x_199, x_193, x_14, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_207);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2(x_4, x_5, x_3, x_199, x_210, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
lean_dec(x_199);
x_213 = lean_ctor_get(x_209, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_215 = x_209;
} else {
 lean_dec_ref(x_209);
 x_215 = lean_box(0);
}
x_216 = l_Lean_Exception_isInterrupt(x_213);
if (x_216 == 0)
{
uint8_t x_217; 
x_217 = l_Lean_Exception_isRuntime(x_213);
if (x_217 == 0)
{
uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_215);
lean_dec(x_213);
x_218 = 0;
x_219 = l_Lean_Elab_Tactic_SavedState_restore(x_207, x_218, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_214);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_box(x_5);
x_222 = lean_apply_11(x_4, x_221, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_222, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_229 = x_222;
} else {
 lean_dec_ref(x_222);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; 
lean_dec(x_207);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_215)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_215;
}
lean_ctor_set(x_231, 0, x_213);
lean_ctor_set(x_231, 1, x_214);
return x_231;
}
}
else
{
lean_object* x_232; 
lean_dec(x_207);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_215)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_215;
}
lean_ctor_set(x_232, 0, x_213);
lean_ctor_set(x_232, 1, x_214);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_204);
lean_dec(x_199);
x_233 = lean_box(x_5);
x_234 = lean_apply_11(x_4, x_233, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_205);
return x_234;
}
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_inc(x_3);
x_253 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__1), 10, 1);
lean_closure_set(x_253, 0, x_3);
x_286 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_15);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_14);
lean_inc(x_193);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_289 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_253, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_287);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_254 = x_290;
x_255 = x_291;
goto block_285;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_292 = lean_ctor_get(x_289, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_289, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_294 = x_289;
} else {
 lean_dec_ref(x_289);
 x_294 = lean_box(0);
}
x_295 = l_Lean_Exception_isInterrupt(x_292);
if (x_295 == 0)
{
uint8_t x_296; 
x_296 = l_Lean_Exception_isRuntime(x_292);
if (x_296 == 0)
{
uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_294);
lean_dec(x_292);
x_297 = 0;
x_298 = l_Lean_Elab_Tactic_SavedState_restore(x_287, x_297, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_293);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_300 = lean_box(0);
x_254 = x_300;
x_255 = x_299;
goto block_285;
}
else
{
lean_object* x_301; 
lean_dec(x_287);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_294)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_294;
}
lean_ctor_set(x_301, 0, x_292);
lean_ctor_set(x_301, 1, x_293);
return x_301;
}
}
else
{
lean_object* x_302; 
lean_dec(x_287);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_294)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_294;
}
lean_ctor_set(x_302, 0, x_292);
lean_ctor_set(x_302, 1, x_293);
return x_302;
}
}
block_285:
{
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = l_Lean_Elab_Tactic_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_255);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_14);
lean_inc(x_193);
lean_inc(x_3);
x_259 = l_Lean_realizeGlobalConstNoOverload(x_3, x_193, x_14, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_257);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__3(x_4, x_5, x_3, x_260, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_261);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = lean_ctor_get(x_259, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_259, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_265 = x_259;
} else {
 lean_dec_ref(x_259);
 x_265 = lean_box(0);
}
x_266 = l_Lean_Exception_isInterrupt(x_263);
if (x_266 == 0)
{
uint8_t x_267; 
x_267 = l_Lean_Exception_isRuntime(x_263);
if (x_267 == 0)
{
uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_265);
lean_dec(x_263);
x_268 = 0;
x_269 = l_Lean_Elab_Tactic_SavedState_restore(x_257, x_268, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_264);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_box(x_5);
x_272 = lean_apply_11(x_4, x_271, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_270);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_272, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_272, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_279 = x_272;
} else {
 lean_dec_ref(x_272);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; 
lean_dec(x_257);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_265)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_265;
}
lean_ctor_set(x_281, 0, x_263);
lean_ctor_set(x_281, 1, x_264);
return x_281;
}
}
else
{
lean_object* x_282; 
lean_dec(x_257);
lean_dec(x_193);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_265)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_265;
}
lean_ctor_set(x_282, 0, x_263);
lean_ctor_set(x_282, 1, x_264);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_254);
x_283 = lean_box(x_5);
x_284 = lean_apply_11(x_4, x_283, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_193, x_14, x_255);
return x_284;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_nat_dec_lt(x_9, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_8);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_nat_mul(x_9, x_24);
x_26 = l_Lean_instInhabitedSyntax;
x_27 = lean_array_get(x_26, x_2, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_25, x_28);
lean_dec(x_25);
x_30 = lean_nat_dec_lt(x_29, x_5);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Syntax_getArg(x_27, x_31);
x_33 = l_Lean_Syntax_isNone(x_32);
lean_dec(x_32);
x_34 = l_Lean_Syntax_getArg(x_27, x_28);
x_35 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__2;
lean_inc(x_34);
x_36 = l_Lean_Syntax_isOfKind(x_34, x_35);
if (x_30 == 0)
{
lean_object* x_65; 
lean_dec(x_29);
x_65 = lean_box(0);
x_37 = x_65;
goto block_64;
}
else
{
lean_object* x_66; 
x_66 = lean_array_fget(x_2, x_29);
lean_dec(x_29);
x_37 = x_66;
goto block_64;
}
block_64:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_inc(x_3);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
lean_inc(x_27);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_mk(x_39);
x_41 = lean_box(2);
lean_inc(x_4);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
lean_ctor_set(x_42, 2, x_40);
x_43 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_42, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (x_33 == 0)
{
uint8_t x_62; 
x_62 = 1;
x_44 = x_62;
goto block_61;
}
else
{
uint8_t x_63; 
x_63 = 0;
x_44 = x_63;
goto block_61;
}
block_61:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_box(x_36);
x_48 = lean_box(x_44);
lean_inc(x_1);
x_49 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___boxed), 15, 6);
lean_closure_set(x_49, 0, x_27);
lean_closure_set(x_49, 1, x_47);
lean_closure_set(x_49, 2, x_34);
lean_closure_set(x_49, 3, x_1);
lean_closure_set(x_49, 4, x_48);
lean_closure_set(x_49, 5, x_35);
x_50 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__5), 11, 1);
lean_closure_set(x_50, 0, x_45);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_51 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Tactic_evalTactic_eval___spec__3(x_49, x_50, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_7, 2);
x_54 = lean_nat_add(x_9, x_53);
lean_dec(x_9);
x_55 = lean_box(0);
x_8 = x_55;
x_9 = x_54;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_20 = x_52;
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_withRWRulesSeq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_withRWRulesSeq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_Tactic_saveTacticInfoForToken___spec__1___rarg___boxed), 10, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_mk(x_20);
x_22 = lean_box(2);
x_23 = l_Lean_Elab_Tactic_withRWRulesSeq___closed__2;
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
x_25 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__5), 11, 1);
lean_closure_set(x_28, 0, x_26);
x_29 = l_Lean_Elab_Tactic_withRWRulesSeq___closed__3;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__21(x_29, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_array_get_size(x_17);
x_33 = lean_nat_add(x_32, x_15);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_div(x_33, x_34);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_15);
x_37 = lean_box(0);
x_38 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1(x_3, x_17, x_18, x_23, x_32, x_36, x_36, x_37, x_13, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_17);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_30);
if (x_47 == 0)
{
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_30, 0);
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_30);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__3(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4(x_1, x_16, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withRWRulesSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_withRWRulesSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Rewrite", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Config", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1;
x_2 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__1;
x_3 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__2;
x_4 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4;
x_10 = 0;
x_11 = l_Lean_Meta_evalExpr_x27___rarg(x_9, x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabRewriteConfig___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_14, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_22, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356_(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = l_Lean_Exception_isInterrupt(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_10);
x_20 = l_Lean_MessageData_ofExpr(x_1);
x_21 = l_Lean_indentD(x_20);
x_22 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Exception_toMessageData(x_16);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_elabRewriteConfig___spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = l_Lean_Exception_isInterrupt(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Exception_isRuntime(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = l_Lean_MessageData_ofExpr(x_1);
x_40 = l_Lean_indentD(x_39);
x_41 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Exception_toMessageData(x_35);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_elabRewriteConfig___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_36);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_35);
lean_ctor_set(x_55, 1, x_36);
return x_55;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasSorry(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__2;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 2;
x_2 = 1;
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_1, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_hasSyntheticSorry(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2(x_14, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1;
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l_Lean_Expr_hasSyntheticSorry(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2(x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__4;
x_2 = l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4;
x_16 = l_Lean_Environment_contains(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__5;
x_18 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_12 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_13 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(x_12);
x_14 = l_Array_isEmpty___rarg(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_8, 5);
x_17 = l_Lean_replaceRef(x_1, x_16);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_17);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4(x_11, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
x_26 = lean_ctor_get(x_8, 6);
x_27 = lean_ctor_get(x_8, 7);
x_28 = lean_ctor_get(x_8, 8);
x_29 = lean_ctor_get(x_8, 9);
x_30 = lean_ctor_get(x_8, 10);
x_31 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_32 = lean_ctor_get(x_8, 11);
x_33 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_32);
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
lean_inc(x_20);
lean_dec(x_8);
x_34 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_23);
lean_ctor_set(x_35, 4, x_24);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_26);
lean_ctor_set(x_35, 7, x_27);
lean_ctor_set(x_35, 8, x_28);
lean_ctor_set(x_35, 9, x_29);
lean_ctor_set(x_35, 10, x_30);
lean_ctor_set(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*12, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*12 + 1, x_33);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4(x_11, x_13, x_36, x_4, x_5, x_6, x_7, x_35, x_9, x_10);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabRewriteConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_elabRewriteConfig___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabRewriteConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabRewriteConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrite", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("did not find instance of the pattern in the current goal", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__2;
x_12 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__6;
x_13 = l_Lean_Meta_throwTacticEx___rarg(x_11, x_1, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_box(x_3);
lean_inc(x_1);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__1___boxed), 13, 3);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_1);
x_16 = lean_box(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_1);
x_18 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___closed__1;
x_19 = l_Lean_Elab_Tactic_withLocation(x_2, x_15, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_elabRewriteConfig(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Elab_Tactic_expandOptLocation(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___boxed), 13, 2);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_18);
x_24 = l_Lean_Elab_Tactic_withRWRulesSeq(x_20, x_22, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRewriteSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewriteSeq", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1;
x_2 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRewriteSeq", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__7;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__6;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__8;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(78u);
x_2 = lean_unsigned_to_nat(91u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(91u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(66u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(52u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(66u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__1);
l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_rewriteTarget___spec__1___rarg___closed__2);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__1 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__1);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__2 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__2);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__3 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__4);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__5 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__5);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__6);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__7 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__7);
l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__8 = _init_l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq_go___closed__8);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__2___closed__2);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__2);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__3 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__3);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__4 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__4();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__4);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__5 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__5();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___lambda__4___closed__5);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_Tactic_withRWRulesSeq___spec__1___closed__2);
l_Lean_Elab_Tactic_withRWRulesSeq___closed__1 = _init_l_Lean_Elab_Tactic_withRWRulesSeq___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq___closed__1);
l_Lean_Elab_Tactic_withRWRulesSeq___closed__2 = _init_l_Lean_Elab_Tactic_withRWRulesSeq___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq___closed__2);
l_Lean_Elab_Tactic_withRWRulesSeq___closed__3 = _init_l_Lean_Elab_Tactic_withRWRulesSeq___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_withRWRulesSeq___closed__3);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__1 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__2 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__2);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__3 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__3);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Rewrite___hyg_1356____closed__4);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__2);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__3);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__1___closed__4);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__1);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__2___closed__2);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__3___closed__1);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__1);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__2);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__3);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__4);
l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabRewriteConfig___lambda__4___closed__5);
l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__3);
l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__4);
l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__5 = _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__5);
l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__6 = _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__2___closed__6);
l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewriteSeq___lambda__3___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__7);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__8);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
