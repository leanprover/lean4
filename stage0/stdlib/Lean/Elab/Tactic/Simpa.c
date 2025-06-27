// Lean compiler output
// Module: Lean.Elab.Tactic.Simpa
// Imports: Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.TryThis Lean.Elab.Tactic.Simp Lean.Elab.App Lean.Linter.Basic
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
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3;
LEAN_EXPORT lean_object* l_linter_unnecessarySimpa;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4;
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4;
lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4;
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__10;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___boxed(lean_object**);
lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__9;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__6____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
static lean_object* l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__8;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__4;
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_initFn___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__12;
static lean_object* l_initFn___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1;
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
extern lean_object* l_Lean_Linter_linterSetsExt;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5;
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3;
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5;
static lean_object* l_initFn___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5;
static lean_object* l_initFn___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1;
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__8____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__6;
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__7;
static lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__1;
static lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
static lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__3;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3;
lean_object* l_Lean_reprExpr____x40_Lean_Expr___hyg_2896_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__7____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5;
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__0;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__2;
lean_object* l_Lean_Elab_Tactic_closeMainGoal___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object**);
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
static lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__5;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__8;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__12;
static lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6;
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_initFn___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
static lean_object* l_initFn___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__2;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7;
static lean_object* _init_l_initFn___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linter", 6, 6);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unnecessarySimpa", 16, 16);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
x_2 = l_initFn___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_initFn___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enable the 'unnecessary simpa' linter", 37, 37);
return x_1;
}
}
static lean_object* _init_l_initFn___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_initFn___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
x_2 = l_initFn___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_initFn___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
x_3 = l_initFn___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
x_4 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_2, x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_linter_unnecessarySimpa;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_3 = l_Lean_Linter_getLinterValue(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.no", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.postpone", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__6____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.yes", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__7____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__6____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__8____x40_Lean_Elab_Tactic_Simpa___hyg_51_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__7____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1024u);
x_20 = lean_nat_dec_le(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_3 = x_21;
goto block_10;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_3 = x_22;
goto block_10;
}
}
case 1:
{
lean_object* x_23; lean_object* x_24; lean_object* x_35; uint8_t x_36; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_24 = x_37;
goto block_34;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_24 = x_38;
goto block_34;
}
block_34:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_25 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__8____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_26 = lean_unsigned_to_nat(1024u);
x_27 = l_Lean_reprExpr____x40_Lean_Expr___hyg_2896_(x_23, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = l_Repr_addAppParen(x_31, x_2);
return x_33;
}
}
default: 
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_11 = x_41;
goto block_18;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_11 = x_42;
goto block_18;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_51_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__0;
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Linter_linterSetsExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0;
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_11, x_8, x_7, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0;
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_20, x_17, x_16, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_1, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_10, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_logAt___at___Lean_logErrorAt___at___Lean_Elab_logException___at___Lean_Elab_Tactic_closeUsingOrAdmit_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("note: this linter can be disabled with `set_option ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" false`", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_initFn___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_4_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1;
lean_inc(x_14);
x_17 = l_Lean_MessageData_ofName(x_14);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
x_18 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
x_22 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__6;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg(x_2, x_26, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1;
lean_inc(x_28);
x_30 = l_Lean_MessageData_ofName(x_28);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
x_36 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__6;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg(x_2, x_40, x_8, x_9, x_10, x_11, x_12);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_8, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___redArg(x_1, x_2, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_8, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___redArg(x_1, x_2, x_8, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_name_eq(x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_14 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___redArg(x_2, x_3, x_9, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___redArg(x_2, x_19, x_9, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0;
lean_ctor_set(x_21, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_20, 0, x_31);
return x_20;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_34 = x_21;
} else {
 lean_dec_ref(x_21);
 x_34 = lean_box(0);
}
x_35 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0;
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_2 = x_41;
x_3 = x_40;
x_12 = x_39;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_dec(x_14);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_dec(x_15);
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(x_1, x_45, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_47 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_23; 
x_23 = l_Lean_Expr_hasExprMVar(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_24 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; uint8_t x_43; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_array_get_size(x_28);
x_30 = l_Lean_Expr_hash(x_2);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_28, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(x_2, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
if (x_43 == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_3);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_83 = lean_ctor_get(x_3, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_3, 0);
lean_dec(x_84);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_27, x_85);
lean_dec(x_27);
lean_inc(x_2);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_44);
lean_ctor_set(x_87, 2, x_42);
x_88 = lean_array_uset(x_28, x_41, x_87);
x_89 = lean_unsigned_to_nat(4u);
x_90 = lean_nat_mul(x_86, x_89);
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_nat_div(x_90, x_91);
lean_dec(x_90);
x_93 = lean_array_get_size(x_88);
x_94 = lean_nat_dec_le(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_88);
lean_ctor_set(x_3, 1, x_95);
lean_ctor_set(x_3, 0, x_86);
x_45 = x_3;
goto block_81;
}
else
{
lean_ctor_set(x_3, 1, x_88);
lean_ctor_set(x_3, 0, x_86);
x_45 = x_3;
goto block_81;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_3);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_27, x_96);
lean_dec(x_27);
lean_inc(x_2);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_44);
lean_ctor_set(x_98, 2, x_42);
x_99 = lean_array_uset(x_28, x_41, x_98);
x_100 = lean_unsigned_to_nat(4u);
x_101 = lean_nat_mul(x_97, x_100);
x_102 = lean_unsigned_to_nat(3u);
x_103 = lean_nat_div(x_101, x_102);
lean_dec(x_101);
x_104 = lean_array_get_size(x_99);
x_105 = lean_nat_dec_le(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_99);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_106);
x_45 = x_107;
goto block_81;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_99);
x_45 = x_108;
goto block_81;
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_28);
lean_dec(x_27);
x_45 = x_3;
goto block_81;
}
block_81:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5(x_1, x_46, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_47;
}
case 5:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(x_1, x_48, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_49);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_2 = x_49;
x_3 = x_54;
x_12 = x_53;
goto _start;
}
}
case 6:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
lean_dec(x_2);
x_13 = x_56;
x_14 = x_57;
x_15 = x_45;
goto block_22;
}
case 7:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_dec(x_2);
x_13 = x_58;
x_14 = x_59;
x_15 = x_45;
goto block_22;
}
case 8:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 3);
lean_inc(x_62);
lean_dec(x_2);
x_63 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(x_1, x_60, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(x_1, x_61, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_62);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_2 = x_62;
x_3 = x_72;
x_12 = x_71;
goto _start;
}
}
}
case 10:
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_dec(x_2);
x_2 = x_74;
x_3 = x_45;
goto _start;
}
case 11:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_2, 2);
lean_inc(x_76);
lean_dec(x_2);
x_2 = x_76;
x_3 = x_45;
goto _start;
}
default: 
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_78 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_45);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_12);
return x_80;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_42);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_109 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_3);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_12);
return x_111;
}
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(x_1, x_13, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_2 = x_14;
x_3 = x_20;
x_12 = x_19;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasExprMVar(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__4;
x_16 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = lean_box(x_12);
lean_ctor_set(x_16, 0, x_27);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_box(x_12);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_SourceInfo_fromRef(x_10, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_10, 5);
lean_inc(x_13);
x_14 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_13);
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2;
lean_inc(x_11);
lean_inc(x_10);
x_23 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_20, x_21, x_22, x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_apply_10(x_2, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("using", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSimpa!_", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpa!", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__10;
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_unsigned_to_nat(105u);
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__9;
x_5 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__8;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tactic_simp_trace;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, uint8_t x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32, lean_object* x_33) {
_start:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_377; uint8_t x_432; lean_object* x_436; uint8_t x_437; 
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
lean_inc(x_24);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed), 11, 1);
lean_closure_set(x_35, 0, x_24);
x_436 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__12;
x_437 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_34, x_436);
lean_dec(x_34);
if (x_437 == 0)
{
if (lean_obj_tag(x_22) == 0)
{
x_432 = x_437;
goto block_435;
}
else
{
x_432 = x_23;
goto block_435;
}
}
else
{
goto block_431;
}
block_58:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Array_append___redArg(x_2, x_52);
lean_dec(x_52);
lean_inc(x_50);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_3);
lean_ctor_set(x_54, 2, x_53);
lean_inc(x_50);
x_55 = l_Lean_Syntax_node5(x_50, x_4, x_41, x_36, x_51, x_43, x_54);
lean_inc(x_39);
x_56 = l_Lean_Syntax_node4(x_50, x_9, x_37, x_39, x_39, x_55);
x_57 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_35, x_56, x_47, x_38, x_49, x_44, x_46, x_42, x_45, x_40, x_48);
return x_57;
}
block_83:
{
lean_object* x_76; lean_object* x_77; 
lean_inc(x_2);
x_76 = l_Array_append___redArg(x_2, x_75);
lean_dec(x_75);
lean_inc(x_3);
lean_inc(x_73);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_3);
lean_ctor_set(x_77, 2, x_76);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_78; 
x_78 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_36 = x_59;
x_37 = x_60;
x_38 = x_61;
x_39 = x_62;
x_40 = x_63;
x_41 = x_64;
x_42 = x_65;
x_43 = x_77;
x_44 = x_66;
x_45 = x_67;
x_46 = x_68;
x_47 = x_70;
x_48 = x_71;
x_49 = x_72;
x_50 = x_73;
x_51 = x_74;
x_52 = x_78;
goto block_58;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__1;
lean_inc(x_73);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Array_mkArray2___redArg(x_81, x_79);
x_36 = x_59;
x_37 = x_60;
x_38 = x_61;
x_39 = x_62;
x_40 = x_63;
x_41 = x_64;
x_42 = x_65;
x_43 = x_77;
x_44 = x_66;
x_45 = x_67;
x_46 = x_68;
x_47 = x_70;
x_48 = x_71;
x_49 = x_72;
x_50 = x_73;
x_51 = x_74;
x_52 = x_82;
goto block_58;
}
}
block_115:
{
lean_object* x_101; lean_object* x_102; 
lean_inc(x_2);
x_101 = l_Array_append___redArg(x_2, x_100);
lean_dec(x_100);
lean_inc(x_3);
lean_inc(x_99);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_3);
lean_ctor_set(x_102, 2, x_101);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_103 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_59 = x_84;
x_60 = x_85;
x_61 = x_87;
x_62 = x_88;
x_63 = x_89;
x_64 = x_90;
x_65 = x_91;
x_66 = x_92;
x_67 = x_93;
x_68 = x_94;
x_69 = x_95;
x_70 = x_96;
x_71 = x_97;
x_72 = x_98;
x_73 = x_99;
x_74 = x_102;
x_75 = x_103;
goto block_83;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
lean_dec(x_86);
x_105 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2;
x_106 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_105);
x_107 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3;
lean_inc(x_99);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_2);
x_109 = l_Array_append___redArg(x_2, x_104);
lean_dec(x_104);
lean_inc(x_3);
lean_inc(x_99);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_109);
x_111 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4;
lean_inc(x_99);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_99);
x_113 = l_Lean_Syntax_node3(x_99, x_106, x_108, x_110, x_112);
x_114 = l_Array_mkArray1___redArg(x_113);
x_59 = x_84;
x_60 = x_85;
x_61 = x_87;
x_62 = x_88;
x_63 = x_89;
x_64 = x_90;
x_65 = x_91;
x_66 = x_92;
x_67 = x_93;
x_68 = x_94;
x_69 = x_95;
x_70 = x_96;
x_71 = x_97;
x_72 = x_98;
x_73 = x_99;
x_74 = x_102;
x_75 = x_114;
goto block_83;
}
}
block_141:
{
lean_object* x_133; lean_object* x_134; 
lean_inc(x_2);
x_133 = l_Array_append___redArg(x_2, x_132);
lean_dec(x_132);
lean_inc(x_3);
lean_inc(x_131);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_3);
lean_ctor_set(x_134, 2, x_133);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_135; 
x_135 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_84 = x_134;
x_85 = x_116;
x_86 = x_118;
x_87 = x_119;
x_88 = x_120;
x_89 = x_121;
x_90 = x_122;
x_91 = x_123;
x_92 = x_124;
x_93 = x_125;
x_94 = x_126;
x_95 = x_127;
x_96 = x_128;
x_97 = x_129;
x_98 = x_130;
x_99 = x_131;
x_100 = x_135;
goto block_115;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_117, 0);
lean_inc(x_136);
lean_dec(x_117);
x_137 = l_Lean_SourceInfo_fromRef(x_136, x_8);
lean_dec(x_136);
x_138 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5;
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Array_mkArray1___redArg(x_139);
x_84 = x_134;
x_85 = x_116;
x_86 = x_118;
x_87 = x_119;
x_88 = x_120;
x_89 = x_121;
x_90 = x_122;
x_91 = x_123;
x_92 = x_124;
x_93 = x_125;
x_94 = x_126;
x_95 = x_127;
x_96 = x_128;
x_97 = x_129;
x_98 = x_130;
x_99 = x_131;
x_100 = x_140;
goto block_115;
}
}
block_164:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = l_Array_append___redArg(x_2, x_158);
lean_dec(x_158);
lean_inc(x_145);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_145);
lean_ctor_set(x_160, 1, x_3);
lean_ctor_set(x_160, 2, x_159);
lean_inc(x_145);
x_161 = l_Lean_Syntax_node5(x_145, x_4, x_149, x_155, x_143, x_146, x_160);
x_162 = l_Lean_Syntax_node2(x_145, x_156, x_147, x_161);
x_163 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_35, x_162, x_154, x_144, x_157, x_151, x_153, x_150, x_152, x_148, x_142);
return x_163;
}
block_189:
{
lean_object* x_182; lean_object* x_183; 
lean_inc(x_2);
x_182 = l_Array_append___redArg(x_2, x_181);
lean_dec(x_181);
lean_inc(x_3);
lean_inc(x_168);
x_183 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_183, 0, x_168);
lean_ctor_set(x_183, 1, x_3);
lean_ctor_set(x_183, 2, x_182);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_184; 
x_184 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_142 = x_165;
x_143 = x_166;
x_144 = x_167;
x_145 = x_168;
x_146 = x_183;
x_147 = x_169;
x_148 = x_170;
x_149 = x_171;
x_150 = x_172;
x_151 = x_173;
x_152 = x_174;
x_153 = x_175;
x_154 = x_177;
x_155 = x_178;
x_156 = x_180;
x_157 = x_179;
x_158 = x_184;
goto block_164;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_176, 0);
lean_inc(x_185);
lean_dec(x_176);
x_186 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__1;
lean_inc(x_168);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_168);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Array_mkArray2___redArg(x_187, x_185);
x_142 = x_165;
x_143 = x_166;
x_144 = x_167;
x_145 = x_168;
x_146 = x_183;
x_147 = x_169;
x_148 = x_170;
x_149 = x_171;
x_150 = x_172;
x_151 = x_173;
x_152 = x_174;
x_153 = x_175;
x_154 = x_177;
x_155 = x_178;
x_156 = x_180;
x_157 = x_179;
x_158 = x_188;
goto block_164;
}
}
block_221:
{
lean_object* x_207; lean_object* x_208; 
lean_inc(x_2);
x_207 = l_Array_append___redArg(x_2, x_206);
lean_dec(x_206);
lean_inc(x_3);
lean_inc(x_193);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_193);
lean_ctor_set(x_208, 1, x_3);
lean_ctor_set(x_208, 2, x_207);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_209; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_209 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_165 = x_191;
x_166 = x_208;
x_167 = x_192;
x_168 = x_193;
x_169 = x_194;
x_170 = x_195;
x_171 = x_196;
x_172 = x_197;
x_173 = x_198;
x_174 = x_199;
x_175 = x_200;
x_176 = x_201;
x_177 = x_202;
x_178 = x_203;
x_179 = x_205;
x_180 = x_204;
x_181 = x_209;
goto block_189;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_210 = lean_ctor_get(x_190, 0);
lean_inc(x_210);
lean_dec(x_190);
x_211 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2;
x_212 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_211);
x_213 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3;
lean_inc(x_193);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_193);
lean_ctor_set(x_214, 1, x_213);
lean_inc(x_2);
x_215 = l_Array_append___redArg(x_2, x_210);
lean_dec(x_210);
lean_inc(x_3);
lean_inc(x_193);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_193);
lean_ctor_set(x_216, 1, x_3);
lean_ctor_set(x_216, 2, x_215);
x_217 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4;
lean_inc(x_193);
x_218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_218, 0, x_193);
lean_ctor_set(x_218, 1, x_217);
lean_inc(x_193);
x_219 = l_Lean_Syntax_node3(x_193, x_212, x_214, x_216, x_218);
x_220 = l_Array_mkArray1___redArg(x_219);
x_165 = x_191;
x_166 = x_208;
x_167 = x_192;
x_168 = x_193;
x_169 = x_194;
x_170 = x_195;
x_171 = x_196;
x_172 = x_197;
x_173 = x_198;
x_174 = x_199;
x_175 = x_200;
x_176 = x_201;
x_177 = x_202;
x_178 = x_203;
x_179 = x_205;
x_180 = x_204;
x_181 = x_220;
goto block_189;
}
}
block_247:
{
lean_object* x_239; lean_object* x_240; 
lean_inc(x_2);
x_239 = l_Array_append___redArg(x_2, x_238);
lean_dec(x_238);
lean_inc(x_3);
lean_inc(x_226);
x_240 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_240, 0, x_226);
lean_ctor_set(x_240, 1, x_3);
lean_ctor_set(x_240, 2, x_239);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_241; 
x_241 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_190 = x_223;
x_191 = x_224;
x_192 = x_225;
x_193 = x_226;
x_194 = x_227;
x_195 = x_228;
x_196 = x_229;
x_197 = x_230;
x_198 = x_231;
x_199 = x_232;
x_200 = x_233;
x_201 = x_234;
x_202 = x_235;
x_203 = x_240;
x_204 = x_237;
x_205 = x_236;
x_206 = x_241;
goto block_221;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_222, 0);
lean_inc(x_242);
lean_dec(x_222);
x_243 = l_Lean_SourceInfo_fromRef(x_242, x_8);
lean_dec(x_242);
x_244 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5;
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Array_mkArray1___redArg(x_245);
x_190 = x_223;
x_191 = x_224;
x_192 = x_225;
x_193 = x_226;
x_194 = x_227;
x_195 = x_228;
x_196 = x_229;
x_197 = x_230;
x_198 = x_231;
x_199 = x_232;
x_200 = x_233;
x_201 = x_234;
x_202 = x_235;
x_203 = x_240;
x_204 = x_237;
x_205 = x_236;
x_206 = x_246;
goto block_221;
}
}
block_312:
{
if (x_10 == 0)
{
lean_object* x_262; 
lean_inc(x_252);
lean_inc(x_257);
lean_inc(x_253);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_260);
lean_inc(x_250);
lean_inc(x_258);
x_262 = lean_apply_9(x_11, x_258, x_250, x_260, x_255, x_256, x_253, x_257, x_252, x_251);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_st_ref_get(x_252, x_264);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_265, 1);
x_268 = lean_ctor_get(x_265, 0);
lean_dec(x_268);
lean_inc(x_263);
lean_ctor_set_tag(x_265, 2);
lean_ctor_set(x_265, 1, x_12);
lean_ctor_set(x_265, 0, x_263);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_263);
x_269 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_3);
lean_ctor_set(x_269, 2, x_2);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_270; 
x_270 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_116 = x_265;
x_117 = x_248;
x_118 = x_249;
x_119 = x_250;
x_120 = x_269;
x_121 = x_252;
x_122 = x_254;
x_123 = x_253;
x_124 = x_255;
x_125 = x_257;
x_126 = x_256;
x_127 = x_259;
x_128 = x_258;
x_129 = x_267;
x_130 = x_260;
x_131 = x_263;
x_132 = x_270;
goto block_141;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_261, 0);
lean_inc(x_271);
lean_dec(x_261);
x_272 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_273 = lean_array_push(x_272, x_271);
x_116 = x_265;
x_117 = x_248;
x_118 = x_249;
x_119 = x_250;
x_120 = x_269;
x_121 = x_252;
x_122 = x_254;
x_123 = x_253;
x_124 = x_255;
x_125 = x_257;
x_126 = x_256;
x_127 = x_259;
x_128 = x_258;
x_129 = x_267;
x_130 = x_260;
x_131 = x_263;
x_132 = x_273;
goto block_141;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_265, 1);
lean_inc(x_274);
lean_dec(x_265);
lean_inc(x_263);
x_275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_275, 0, x_263);
lean_ctor_set(x_275, 1, x_12);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_263);
x_276 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_276, 0, x_263);
lean_ctor_set(x_276, 1, x_3);
lean_ctor_set(x_276, 2, x_2);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_277; 
x_277 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_116 = x_275;
x_117 = x_248;
x_118 = x_249;
x_119 = x_250;
x_120 = x_276;
x_121 = x_252;
x_122 = x_254;
x_123 = x_253;
x_124 = x_255;
x_125 = x_257;
x_126 = x_256;
x_127 = x_259;
x_128 = x_258;
x_129 = x_274;
x_130 = x_260;
x_131 = x_263;
x_132 = x_277;
goto block_141;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_261, 0);
lean_inc(x_278);
lean_dec(x_261);
x_279 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_280 = lean_array_push(x_279, x_278);
x_116 = x_275;
x_117 = x_248;
x_118 = x_249;
x_119 = x_250;
x_120 = x_276;
x_121 = x_252;
x_122 = x_254;
x_123 = x_253;
x_124 = x_255;
x_125 = x_257;
x_126 = x_256;
x_127 = x_259;
x_128 = x_258;
x_129 = x_274;
x_130 = x_260;
x_131 = x_263;
x_132 = x_280;
goto block_141;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_262);
if (x_281 == 0)
{
return x_262;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_262, 0);
x_283 = lean_ctor_get(x_262, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_262);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
else
{
lean_object* x_285; 
lean_dec(x_12);
lean_dec(x_9);
lean_inc(x_252);
lean_inc(x_257);
lean_inc(x_253);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_260);
lean_inc(x_250);
lean_inc(x_258);
x_285 = lean_apply_9(x_11, x_258, x_250, x_260, x_255, x_256, x_253, x_257, x_252, x_251);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_st_ref_get(x_252, x_287);
x_289 = !lean_is_exclusive(x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_288, 1);
x_291 = lean_ctor_get(x_288, 0);
lean_dec(x_291);
x_292 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__6;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_293 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_292);
x_294 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__7;
lean_inc(x_286);
lean_ctor_set_tag(x_288, 2);
lean_ctor_set(x_288, 1, x_294);
lean_ctor_set(x_288, 0, x_286);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_295; 
x_295 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_222 = x_248;
x_223 = x_249;
x_224 = x_290;
x_225 = x_250;
x_226 = x_286;
x_227 = x_288;
x_228 = x_252;
x_229 = x_254;
x_230 = x_253;
x_231 = x_255;
x_232 = x_257;
x_233 = x_256;
x_234 = x_259;
x_235 = x_258;
x_236 = x_260;
x_237 = x_293;
x_238 = x_295;
goto block_247;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_261, 0);
lean_inc(x_296);
lean_dec(x_261);
x_297 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_298 = lean_array_push(x_297, x_296);
x_222 = x_248;
x_223 = x_249;
x_224 = x_290;
x_225 = x_250;
x_226 = x_286;
x_227 = x_288;
x_228 = x_252;
x_229 = x_254;
x_230 = x_253;
x_231 = x_255;
x_232 = x_257;
x_233 = x_256;
x_234 = x_259;
x_235 = x_258;
x_236 = x_260;
x_237 = x_293;
x_238 = x_298;
goto block_247;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_299 = lean_ctor_get(x_288, 1);
lean_inc(x_299);
lean_dec(x_288);
x_300 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__6;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_301 = l_Lean_Name_mkStr4(x_5, x_6, x_7, x_300);
x_302 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__7;
lean_inc(x_286);
x_303 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_303, 0, x_286);
lean_ctor_set(x_303, 1, x_302);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_304; 
x_304 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_222 = x_248;
x_223 = x_249;
x_224 = x_299;
x_225 = x_250;
x_226 = x_286;
x_227 = x_303;
x_228 = x_252;
x_229 = x_254;
x_230 = x_253;
x_231 = x_255;
x_232 = x_257;
x_233 = x_256;
x_234 = x_259;
x_235 = x_258;
x_236 = x_260;
x_237 = x_301;
x_238 = x_304;
goto block_247;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_261, 0);
lean_inc(x_305);
lean_dec(x_261);
x_306 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_307 = lean_array_push(x_306, x_305);
x_222 = x_248;
x_223 = x_249;
x_224 = x_299;
x_225 = x_250;
x_226 = x_286;
x_227 = x_303;
x_228 = x_252;
x_229 = x_254;
x_230 = x_253;
x_231 = x_255;
x_232 = x_257;
x_233 = x_256;
x_234 = x_259;
x_235 = x_258;
x_236 = x_260;
x_237 = x_301;
x_238 = x_307;
goto block_247;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_285);
if (x_308 == 0)
{
return x_285;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_285, 0);
x_310 = lean_ctor_get(x_285, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_285);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
block_345:
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_328 = lean_unsigned_to_nat(5u);
x_329 = l_Lean_Syntax_getArg(x_315, x_328);
lean_dec(x_315);
x_330 = l_Lean_Syntax_matchesNull(x_329, x_13);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_331 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11;
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
x_332 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_331, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326, x_327);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_35, x_333, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326, x_334);
return x_335;
}
else
{
uint8_t x_336; 
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_35);
lean_dec(x_1);
x_336 = !lean_is_exclusive(x_332);
if (x_336 == 0)
{
return x_332;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_332, 0);
x_338 = lean_ctor_get(x_332, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_332);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
lean_object* x_340; 
x_340 = l_Lean_Syntax_getOptional_x3f(x_313);
lean_dec(x_313);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; 
x_341 = lean_box(0);
x_248 = x_314;
x_249 = x_318;
x_250 = x_320;
x_251 = x_327;
x_252 = x_326;
x_253 = x_324;
x_254 = x_317;
x_255 = x_322;
x_256 = x_323;
x_257 = x_325;
x_258 = x_319;
x_259 = x_316;
x_260 = x_321;
x_261 = x_341;
goto block_312;
}
else
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_340);
if (x_342 == 0)
{
x_248 = x_314;
x_249 = x_318;
x_250 = x_320;
x_251 = x_327;
x_252 = x_326;
x_253 = x_324;
x_254 = x_317;
x_255 = x_322;
x_256 = x_323;
x_257 = x_325;
x_258 = x_319;
x_259 = x_316;
x_260 = x_321;
x_261 = x_340;
goto block_312;
}
else
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
lean_dec(x_340);
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_343);
x_248 = x_314;
x_249 = x_318;
x_250 = x_320;
x_251 = x_327;
x_252 = x_326;
x_253 = x_324;
x_254 = x_317;
x_255 = x_322;
x_256 = x_323;
x_257 = x_325;
x_258 = x_319;
x_259 = x_316;
x_260 = x_321;
x_261 = x_344;
goto block_312;
}
}
}
}
block_376:
{
lean_object* x_360; uint8_t x_361; 
x_360 = l_Lean_Syntax_getArg(x_347, x_14);
x_361 = l_Lean_Syntax_isNone(x_360);
if (x_361 == 0)
{
uint8_t x_362; 
lean_inc(x_360);
x_362 = l_Lean_Syntax_matchesNull(x_360, x_15);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_360);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_363 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11;
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
x_364 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_363, x_351, x_352, x_353, x_354, x_355, x_356, x_357, x_358, x_359);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_35, x_365, x_351, x_352, x_353, x_354, x_355, x_356, x_357, x_358, x_366);
return x_367;
}
else
{
uint8_t x_368; 
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_35);
lean_dec(x_1);
x_368 = !lean_is_exclusive(x_364);
if (x_368 == 0)
{
return x_364;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_364, 0);
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_364);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = l_Lean_Syntax_getArg(x_360, x_16);
lean_dec(x_360);
x_373 = l_Lean_Syntax_getArgs(x_372);
lean_dec(x_372);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_373);
x_313 = x_346;
x_314 = x_350;
x_315 = x_347;
x_316 = x_348;
x_317 = x_349;
x_318 = x_374;
x_319 = x_351;
x_320 = x_352;
x_321 = x_353;
x_322 = x_354;
x_323 = x_355;
x_324 = x_356;
x_325 = x_357;
x_326 = x_358;
x_327 = x_359;
goto block_345;
}
}
else
{
lean_object* x_375; 
lean_dec(x_360);
x_375 = lean_box(0);
x_313 = x_346;
x_314 = x_350;
x_315 = x_347;
x_316 = x_348;
x_317 = x_349;
x_318 = x_375;
x_319 = x_351;
x_320 = x_352;
x_321 = x_353;
x_322 = x_354;
x_323 = x_355;
x_324 = x_356;
x_325 = x_357;
x_326 = x_358;
x_327 = x_359;
goto block_345;
}
}
block_424:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_24, 0);
lean_inc(x_378);
lean_dec(x_24);
x_379 = l_Lean_Syntax_unsetTrailing(x_17);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_380 = l_Lean_Elab_Tactic_mkSimpOnly(x_379, x_378, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_378);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
lean_inc(x_381);
x_383 = l_Lean_Syntax_isOfKind(x_381, x_18);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_384 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11;
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_385 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_384, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_382);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_385, 1);
lean_inc(x_387);
lean_dec(x_385);
x_388 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_35, x_386, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_387);
return x_388;
}
else
{
uint8_t x_389; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_385);
if (x_389 == 0)
{
return x_385;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_385, 0);
x_391 = lean_ctor_get(x_385, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_385);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
lean_object* x_393; uint8_t x_394; 
x_393 = l_Lean_Syntax_getArg(x_381, x_16);
lean_inc(x_393);
x_394 = l_Lean_Syntax_isOfKind(x_393, x_19);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; 
lean_dec(x_393);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_395 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11;
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_396 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_395, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_382);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_35, x_397, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_398);
return x_399;
}
else
{
uint8_t x_400; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_400 = !lean_is_exclusive(x_396);
if (x_400 == 0)
{
return x_396;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_396, 0);
x_402 = lean_ctor_get(x_396, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_396);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_404 = l_Lean_Syntax_getArg(x_381, x_20);
x_405 = l_Lean_Syntax_getArg(x_381, x_15);
x_406 = l_Lean_Syntax_isNone(x_405);
if (x_406 == 0)
{
uint8_t x_407; 
lean_inc(x_405);
x_407 = l_Lean_Syntax_matchesNull(x_405, x_16);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; 
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_393);
lean_dec(x_381);
lean_dec(x_377);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_408 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11;
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_409 = l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0(x_408, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_382);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2(x_1, x_35, x_410, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_411);
return x_412;
}
else
{
uint8_t x_413; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_413 = !lean_is_exclusive(x_409);
if (x_413 == 0)
{
return x_409;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_409, 0);
x_415 = lean_ctor_get(x_409, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_409);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; 
x_417 = l_Lean_Syntax_getArg(x_405, x_13);
lean_dec(x_405);
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_417);
x_346 = x_404;
x_347 = x_381;
x_348 = x_377;
x_349 = x_393;
x_350 = x_418;
x_351 = x_25;
x_352 = x_26;
x_353 = x_27;
x_354 = x_28;
x_355 = x_29;
x_356 = x_30;
x_357 = x_31;
x_358 = x_32;
x_359 = x_382;
goto block_376;
}
}
else
{
lean_object* x_419; 
lean_dec(x_405);
x_419 = lean_box(0);
x_346 = x_404;
x_347 = x_381;
x_348 = x_377;
x_349 = x_393;
x_350 = x_419;
x_351 = x_25;
x_352 = x_26;
x_353 = x_27;
x_354 = x_28;
x_355 = x_29;
x_356 = x_30;
x_357 = x_31;
x_358 = x_32;
x_359 = x_382;
goto block_376;
}
}
}
}
else
{
uint8_t x_420; 
lean_dec(x_377);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_420 = !lean_is_exclusive(x_380);
if (x_420 == 0)
{
return x_380;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_380, 0);
x_422 = lean_ctor_get(x_380, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_380);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
block_431:
{
if (lean_obj_tag(x_21) == 0)
{
x_377 = x_21;
goto block_424;
}
else
{
uint8_t x_425; 
x_425 = !lean_is_exclusive(x_21);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = lean_ctor_get(x_21, 0);
x_427 = l_Lean_Syntax_unsetTrailing(x_426);
lean_ctor_set(x_21, 0, x_427);
x_377 = x_21;
goto block_424;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_21, 0);
lean_inc(x_428);
lean_dec(x_21);
x_429 = l_Lean_Syntax_unsetTrailing(x_428);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_429);
x_377 = x_430;
goto block_424;
}
}
}
block_435:
{
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; 
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_433 = lean_box(0);
x_434 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(x_24, x_433, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
return x_434;
}
else
{
goto block_431;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type mismatch, term", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nafter simplification", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Lean_MVarId_getType(x_1, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_mk_syntax_ident(x_2);
lean_inc(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_24 = l_Lean_Elab_Term_elabTerm(x_22, x_23, x_3, x_3, x_12, x_13, x_14, x_15, x_16, x_17, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_27 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_4, x_12, x_13, x_14, x_15, x_16, x_17, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_25);
x_30 = lean_infer_type(x_25, x_14, x_15, x_16, x_17, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_53 = lean_ctor_get(x_14, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 8);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_14, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_14, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_14, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_14, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_14, 6);
lean_inc(x_60);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
uint8_t x_62; uint8_t x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_63 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
lean_ctor_set_uint8(x_53, 7, x_9);
x_64 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_53);
x_65 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_55);
lean_ctor_set(x_65, 2, x_56);
lean_ctor_set(x_65, 3, x_57);
lean_ctor_set(x_65, 4, x_58);
lean_ctor_set(x_65, 5, x_59);
lean_ctor_set(x_65, 6, x_60);
lean_ctor_set_uint64(x_65, sizeof(void*)*7, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 8, x_54);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 9, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 10, x_63);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_31);
lean_inc(x_20);
x_66 = l_Lean_Meta_isExprDefEq(x_20, x_31, x_65, x_15, x_16, x_17, x_32);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_33 = x_69;
x_34 = x_68;
goto block_52;
}
else
{
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_33 = x_72;
x_34 = x_71;
goto block_52;
}
else
{
uint8_t x_73; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_66);
if (x_73 == 0)
{
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_66);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; lean_object* x_99; 
x_77 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 9);
x_78 = lean_ctor_get_uint8(x_14, sizeof(void*)*7 + 10);
x_79 = lean_ctor_get_uint8(x_53, 0);
x_80 = lean_ctor_get_uint8(x_53, 1);
x_81 = lean_ctor_get_uint8(x_53, 2);
x_82 = lean_ctor_get_uint8(x_53, 3);
x_83 = lean_ctor_get_uint8(x_53, 4);
x_84 = lean_ctor_get_uint8(x_53, 5);
x_85 = lean_ctor_get_uint8(x_53, 6);
x_86 = lean_ctor_get_uint8(x_53, 8);
x_87 = lean_ctor_get_uint8(x_53, 9);
x_88 = lean_ctor_get_uint8(x_53, 10);
x_89 = lean_ctor_get_uint8(x_53, 11);
x_90 = lean_ctor_get_uint8(x_53, 12);
x_91 = lean_ctor_get_uint8(x_53, 13);
x_92 = lean_ctor_get_uint8(x_53, 14);
x_93 = lean_ctor_get_uint8(x_53, 15);
x_94 = lean_ctor_get_uint8(x_53, 16);
x_95 = lean_ctor_get_uint8(x_53, 17);
lean_dec(x_53);
x_96 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_96, 0, x_79);
lean_ctor_set_uint8(x_96, 1, x_80);
lean_ctor_set_uint8(x_96, 2, x_81);
lean_ctor_set_uint8(x_96, 3, x_82);
lean_ctor_set_uint8(x_96, 4, x_83);
lean_ctor_set_uint8(x_96, 5, x_84);
lean_ctor_set_uint8(x_96, 6, x_85);
lean_ctor_set_uint8(x_96, 7, x_9);
lean_ctor_set_uint8(x_96, 8, x_86);
lean_ctor_set_uint8(x_96, 9, x_87);
lean_ctor_set_uint8(x_96, 10, x_88);
lean_ctor_set_uint8(x_96, 11, x_89);
lean_ctor_set_uint8(x_96, 12, x_90);
lean_ctor_set_uint8(x_96, 13, x_91);
lean_ctor_set_uint8(x_96, 14, x_92);
lean_ctor_set_uint8(x_96, 15, x_93);
lean_ctor_set_uint8(x_96, 16, x_94);
lean_ctor_set_uint8(x_96, 17, x_95);
x_97 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_96);
x_98 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_55);
lean_ctor_set(x_98, 2, x_56);
lean_ctor_set(x_98, 3, x_57);
lean_ctor_set(x_98, 4, x_58);
lean_ctor_set(x_98, 5, x_59);
lean_ctor_set(x_98, 6, x_60);
lean_ctor_set_uint64(x_98, sizeof(void*)*7, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*7 + 8, x_54);
lean_ctor_set_uint8(x_98, sizeof(void*)*7 + 9, x_77);
lean_ctor_set_uint8(x_98, sizeof(void*)*7 + 10, x_78);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_31);
lean_inc(x_20);
x_99 = l_Lean_Meta_isExprDefEq(x_20, x_31, x_98, x_15, x_16, x_17, x_32);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_unbox(x_100);
lean_dec(x_100);
x_33 = x_102;
x_34 = x_101;
goto block_52;
}
else
{
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_unbox(x_103);
lean_dec(x_103);
x_33 = x_105;
x_34 = x_104;
goto block_52;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_106 = lean_ctor_get(x_99, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_108 = x_99;
} else {
 lean_dec_ref(x_99);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
block_52:
{
if (x_33 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_35 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1;
x_36 = l_Lean_indentExpr(x_5);
if (lean_is_scalar(x_29)) {
 x_37 = lean_alloc_ctor(7, 2, 0);
} else {
 x_37 = x_29;
 lean_ctor_set_tag(x_37, 7);
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Elab_Term_throwTypeMismatchError___redArg(x_40, x_20, x_31, x_25, x_8, x_14, x_15, x_16, x_17, x_34);
lean_dec(x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
x_42 = l_Lean_Meta_getMVars(x_5, x_14, x_15, x_16, x_17, x_34);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Tactic_filterOldMVars___redArg(x_43, x_6, x_15, x_44);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_48 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_46, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_47);
lean_dec(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Name_mkStr1(x_7);
x_51 = l_Lean_Elab_Tactic_closeMainGoal___redArg(x_50, x_25, x_4, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_49);
return x_51;
}
else
{
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
return x_48;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_110 = !lean_is_exclusive(x_30);
if (x_110 == 0)
{
return x_30;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_30, 0);
x_112 = lean_ctor_get(x_30, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_30);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_114; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_114 = !lean_is_exclusive(x_24);
if (x_114 == 0)
{
return x_24;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_24, 0);
x_116 = lean_ctor_get(x_24, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_24);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_19);
if (x_118 == 0)
{
return x_19;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_19, 0);
x_120 = lean_ctor_get(x_19, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_19);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("this", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("occurs check failed, expression", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ncontains the goal ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
x_62 = lean_ctor_get(x_18, 2);
lean_inc(x_62);
x_63 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1;
x_64 = l_Lean_LocalContext_findFromUserName_x3f(x_62, x_63);
lean_dec(x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_65 = l_Lean_MVarId_assumption(x_2, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_apply_10(x_3, x_4, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_66);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_23 = x_73;
goto block_46;
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_st_ref_get(x_19, x_22);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
x_79 = lean_box(0);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_80 = l_Lean_Elab_Tactic_elabTerm(x_74, x_79, x_10, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_81);
x_83 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(x_2, x_81, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_82);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
lean_dec(x_77);
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_151; 
x_86 = lean_ctor_get(x_83, 0);
x_87 = lean_ctor_get(x_83, 1);
x_88 = lean_ctor_get(x_84, 2);
lean_inc(x_88);
lean_dec(x_84);
x_151 = lean_unbox(x_86);
lean_dec(x_86);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_88);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_152 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3;
x_153 = l_Lean_indentExpr(x_81);
lean_ctor_set_tag(x_83, 7);
lean_ctor_set(x_83, 1, x_153);
lean_ctor_set(x_83, 0, x_152);
x_154 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5;
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_154);
lean_ctor_set(x_75, 0, x_83);
x_155 = l_Lean_Expr_mvar___override(x_2);
x_156 = l_Lean_MessageData_ofExpr(x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_75);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_159, x_18, x_19, x_20, x_21, x_87);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
return x_160;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_160);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_object* x_165; 
lean_free_object(x_83);
lean_free_object(x_75);
lean_inc(x_2);
x_165 = l_Lean_MVarId_getType(x_2, x_18, x_19, x_20, x_21, x_87);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
lean_inc(x_2);
x_168 = l_Lean_MVarId_getTag(x_2, x_18, x_19, x_20, x_21, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_18);
x_171 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_166, x_169, x_18, x_19, x_20, x_21, x_170);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_ctor_get(x_171, 1);
x_175 = l_Lean_Expr_mvarId_x21(x_173);
x_176 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_81);
x_177 = l_Lean_MVarId_note(x_175, x_176, x_81, x_79, x_18, x_19, x_20, x_21, x_174);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_178, 0);
x_182 = lean_ctor_get(x_178, 1);
x_183 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_181);
x_184 = lean_array_push(x_183, x_181);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_185 = l_Lean_Meta_simpGoal(x_182, x_6, x_7, x_8, x_9, x_184, x_4, x_18, x_19, x_20, x_21, x_179);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; uint8_t x_189; 
lean_dec(x_181);
lean_dec(x_88);
lean_dec(x_11);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_186, 1);
x_191 = lean_ctor_get(x_186, 0);
lean_dec(x_191);
lean_inc(x_20);
x_192 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_188);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = lean_ctor_get(x_192, 1);
x_196 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_194);
lean_dec(x_194);
if (x_196 == 0)
{
lean_free_object(x_192);
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_195;
goto block_61;
}
else
{
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_81, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_18, 2);
lean_inc(x_198);
x_199 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_198, x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_free_object(x_192);
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_195;
goto block_61;
}
else
{
lean_dec(x_199);
if (x_12 == 0)
{
lean_free_object(x_192);
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_195;
goto block_61;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_200 = lean_ctor_get(x_20, 5);
lean_inc(x_200);
x_201 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_202 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
x_203 = l_Lean_MessageData_ofExpr(x_81);
lean_inc(x_203);
lean_ctor_set_tag(x_192, 7);
lean_ctor_set(x_192, 1, x_203);
lean_ctor_set(x_192, 0, x_202);
x_204 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
lean_ctor_set_tag(x_186, 7);
lean_ctor_set(x_186, 1, x_204);
lean_ctor_set(x_186, 0, x_192);
lean_ctor_set_tag(x_178, 7);
lean_ctor_set(x_178, 1, x_203);
lean_ctor_set(x_178, 0, x_186);
x_205 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
lean_ctor_set_tag(x_171, 7);
lean_ctor_set(x_171, 1, x_205);
lean_ctor_set(x_171, 0, x_178);
lean_inc(x_20);
x_206 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_201, x_200, x_171, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_195);
lean_dec(x_200);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_207;
goto block_61;
}
}
}
else
{
lean_free_object(x_192);
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_195;
goto block_61;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_192, 0);
x_209 = lean_ctor_get(x_192, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_192);
x_210 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_208);
lean_dec(x_208);
if (x_210 == 0)
{
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_209;
goto block_61;
}
else
{
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_81, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_18, 2);
lean_inc(x_212);
x_213 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_212, x_211);
if (lean_obj_tag(x_213) == 0)
{
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_209;
goto block_61;
}
else
{
lean_dec(x_213);
if (x_12 == 0)
{
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_209;
goto block_61;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_214 = lean_ctor_get(x_20, 5);
lean_inc(x_214);
x_215 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_216 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
x_217 = l_Lean_MessageData_ofExpr(x_81);
lean_inc(x_217);
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
lean_ctor_set_tag(x_186, 7);
lean_ctor_set(x_186, 1, x_219);
lean_ctor_set(x_186, 0, x_218);
lean_ctor_set_tag(x_178, 7);
lean_ctor_set(x_178, 1, x_217);
lean_ctor_set(x_178, 0, x_186);
x_220 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
lean_ctor_set_tag(x_171, 7);
lean_ctor_set(x_171, 1, x_220);
lean_ctor_set(x_171, 0, x_178);
lean_inc(x_20);
x_221 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_215, x_214, x_171, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_209);
lean_dec(x_214);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_222;
goto block_61;
}
}
}
else
{
lean_free_object(x_186);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_190;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_209;
goto block_61;
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_223 = lean_ctor_get(x_186, 1);
lean_inc(x_223);
lean_dec(x_186);
lean_inc(x_20);
x_224 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_188);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_225);
lean_dec(x_225);
if (x_228 == 0)
{
lean_dec(x_227);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_223;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_226;
goto block_61;
}
else
{
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_81, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_18, 2);
lean_inc(x_230);
x_231 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_230, x_229);
if (lean_obj_tag(x_231) == 0)
{
lean_dec(x_227);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_223;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_226;
goto block_61;
}
else
{
lean_dec(x_231);
if (x_12 == 0)
{
lean_dec(x_227);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_223;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_226;
goto block_61;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_232 = lean_ctor_get(x_20, 5);
lean_inc(x_232);
x_233 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_234 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
x_235 = l_Lean_MessageData_ofExpr(x_81);
lean_inc(x_235);
if (lean_is_scalar(x_227)) {
 x_236 = lean_alloc_ctor(7, 2, 0);
} else {
 x_236 = x_227;
 lean_ctor_set_tag(x_236, 7);
}
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
x_238 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set_tag(x_178, 7);
lean_ctor_set(x_178, 1, x_235);
lean_ctor_set(x_178, 0, x_238);
x_239 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
lean_ctor_set_tag(x_171, 7);
lean_ctor_set(x_171, 1, x_239);
lean_ctor_set(x_171, 0, x_178);
lean_inc(x_20);
x_240 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_233, x_232, x_171, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_226);
lean_dec(x_232);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_47 = x_173;
x_48 = x_223;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_241;
goto block_61;
}
}
}
else
{
lean_dec(x_227);
lean_free_object(x_178);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_223;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_226;
goto block_61;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
lean_free_object(x_178);
lean_free_object(x_171);
x_242 = lean_ctor_get(x_187, 0);
lean_inc(x_242);
lean_dec(x_187);
x_243 = lean_ctor_get(x_185, 1);
lean_inc(x_243);
lean_dec(x_185);
x_244 = lean_ctor_get(x_186, 1);
lean_inc(x_244);
lean_dec(x_186);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
lean_dec(x_242);
x_247 = lean_array_get_size(x_245);
x_248 = lean_nat_dec_lt(x_13, x_247);
lean_dec(x_247);
if (x_248 == 0)
{
lean_dec(x_245);
x_89 = x_246;
x_90 = x_173;
x_91 = x_244;
x_92 = x_15;
x_93 = x_21;
x_94 = x_14;
x_95 = x_20;
x_96 = x_16;
x_97 = x_17;
x_98 = x_18;
x_99 = x_176;
x_100 = x_19;
x_101 = x_243;
x_102 = x_181;
goto block_150;
}
else
{
lean_object* x_249; 
lean_dec(x_181);
x_249 = lean_array_fget(x_245, x_13);
lean_dec(x_245);
x_89 = x_246;
x_90 = x_173;
x_91 = x_244;
x_92 = x_15;
x_93 = x_21;
x_94 = x_14;
x_95 = x_20;
x_96 = x_16;
x_97 = x_17;
x_98 = x_18;
x_99 = x_176;
x_100 = x_19;
x_101 = x_243;
x_102 = x_249;
goto block_150;
}
}
}
else
{
uint8_t x_250; 
lean_free_object(x_178);
lean_dec(x_181);
lean_free_object(x_171);
lean_dec(x_173);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_250 = !lean_is_exclusive(x_185);
if (x_250 == 0)
{
return x_185;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_185, 0);
x_252 = lean_ctor_get(x_185, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_185);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_178, 0);
x_255 = lean_ctor_get(x_178, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_178);
x_256 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_254);
x_257 = lean_array_push(x_256, x_254);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_258 = l_Lean_Meta_simpGoal(x_255, x_6, x_7, x_8, x_9, x_257, x_4, x_18, x_19, x_20, x_21, x_179);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
lean_dec(x_254);
lean_dec(x_88);
lean_dec(x_11);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_263 = x_259;
} else {
 lean_dec_ref(x_259);
 x_263 = lean_box(0);
}
lean_inc(x_20);
x_264 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_261);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
x_268 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_265);
lean_dec(x_265);
if (x_268 == 0)
{
lean_dec(x_267);
lean_dec(x_263);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_262;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_266;
goto block_61;
}
else
{
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_81, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_18, 2);
lean_inc(x_270);
x_271 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_270, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_dec(x_267);
lean_dec(x_263);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_262;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_266;
goto block_61;
}
else
{
lean_dec(x_271);
if (x_12 == 0)
{
lean_dec(x_267);
lean_dec(x_263);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_262;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_266;
goto block_61;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_272 = lean_ctor_get(x_20, 5);
lean_inc(x_272);
x_273 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_274 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
x_275 = l_Lean_MessageData_ofExpr(x_81);
lean_inc(x_275);
if (lean_is_scalar(x_267)) {
 x_276 = lean_alloc_ctor(7, 2, 0);
} else {
 x_276 = x_267;
 lean_ctor_set_tag(x_276, 7);
}
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
if (lean_is_scalar(x_263)) {
 x_278 = lean_alloc_ctor(7, 2, 0);
} else {
 x_278 = x_263;
 lean_ctor_set_tag(x_278, 7);
}
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_275);
x_280 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
lean_ctor_set_tag(x_171, 7);
lean_ctor_set(x_171, 1, x_280);
lean_ctor_set(x_171, 0, x_279);
lean_inc(x_20);
x_281 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_273, x_272, x_171, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_266);
lean_dec(x_272);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_47 = x_173;
x_48 = x_262;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_282;
goto block_61;
}
}
}
else
{
lean_dec(x_267);
lean_dec(x_263);
lean_free_object(x_171);
lean_dec(x_81);
x_47 = x_173;
x_48 = x_262;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_266;
goto block_61;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_free_object(x_171);
x_283 = lean_ctor_get(x_260, 0);
lean_inc(x_283);
lean_dec(x_260);
x_284 = lean_ctor_get(x_258, 1);
lean_inc(x_284);
lean_dec(x_258);
x_285 = lean_ctor_get(x_259, 1);
lean_inc(x_285);
lean_dec(x_259);
x_286 = lean_ctor_get(x_283, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_288 = lean_array_get_size(x_286);
x_289 = lean_nat_dec_lt(x_13, x_288);
lean_dec(x_288);
if (x_289 == 0)
{
lean_dec(x_286);
x_89 = x_287;
x_90 = x_173;
x_91 = x_285;
x_92 = x_15;
x_93 = x_21;
x_94 = x_14;
x_95 = x_20;
x_96 = x_16;
x_97 = x_17;
x_98 = x_18;
x_99 = x_176;
x_100 = x_19;
x_101 = x_284;
x_102 = x_254;
goto block_150;
}
else
{
lean_object* x_290; 
lean_dec(x_254);
x_290 = lean_array_fget(x_286, x_13);
lean_dec(x_286);
x_89 = x_287;
x_90 = x_173;
x_91 = x_285;
x_92 = x_15;
x_93 = x_21;
x_94 = x_14;
x_95 = x_20;
x_96 = x_16;
x_97 = x_17;
x_98 = x_18;
x_99 = x_176;
x_100 = x_19;
x_101 = x_284;
x_102 = x_290;
goto block_150;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_254);
lean_free_object(x_171);
lean_dec(x_173);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_291 = lean_ctor_get(x_258, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_258, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_293 = x_258;
} else {
 lean_dec_ref(x_258);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_free_object(x_171);
lean_dec(x_173);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_295 = !lean_is_exclusive(x_177);
if (x_295 == 0)
{
return x_177;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_177, 0);
x_297 = lean_ctor_get(x_177, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_177);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_299 = lean_ctor_get(x_171, 0);
x_300 = lean_ctor_get(x_171, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_171);
x_301 = l_Lean_Expr_mvarId_x21(x_299);
x_302 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_81);
x_303 = l_Lean_MVarId_note(x_301, x_302, x_81, x_79, x_18, x_19, x_20, x_21, x_300);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_ctor_get(x_304, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_304, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_308 = x_304;
} else {
 lean_dec_ref(x_304);
 x_308 = lean_box(0);
}
x_309 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_306);
x_310 = lean_array_push(x_309, x_306);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_311 = l_Lean_Meta_simpGoal(x_307, x_6, x_7, x_8, x_9, x_310, x_4, x_18, x_19, x_20, x_21, x_305);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
lean_dec(x_306);
lean_dec(x_88);
lean_dec(x_11);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_316 = x_312;
} else {
 lean_dec_ref(x_312);
 x_316 = lean_box(0);
}
lean_inc(x_20);
x_317 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_314);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_320 = x_317;
} else {
 lean_dec_ref(x_317);
 x_320 = lean_box(0);
}
x_321 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_318);
lean_dec(x_318);
if (x_321 == 0)
{
lean_dec(x_320);
lean_dec(x_316);
lean_dec(x_308);
lean_dec(x_81);
x_47 = x_299;
x_48 = x_315;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_319;
goto block_61;
}
else
{
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_81, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_18, 2);
lean_inc(x_323);
x_324 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_323, x_322);
if (lean_obj_tag(x_324) == 0)
{
lean_dec(x_320);
lean_dec(x_316);
lean_dec(x_308);
lean_dec(x_81);
x_47 = x_299;
x_48 = x_315;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_319;
goto block_61;
}
else
{
lean_dec(x_324);
if (x_12 == 0)
{
lean_dec(x_320);
lean_dec(x_316);
lean_dec(x_308);
lean_dec(x_81);
x_47 = x_299;
x_48 = x_315;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_319;
goto block_61;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_325 = lean_ctor_get(x_20, 5);
lean_inc(x_325);
x_326 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_327 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
x_328 = l_Lean_MessageData_ofExpr(x_81);
lean_inc(x_328);
if (lean_is_scalar(x_320)) {
 x_329 = lean_alloc_ctor(7, 2, 0);
} else {
 x_329 = x_320;
 lean_ctor_set_tag(x_329, 7);
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
if (lean_is_scalar(x_316)) {
 x_331 = lean_alloc_ctor(7, 2, 0);
} else {
 x_331 = x_316;
 lean_ctor_set_tag(x_331, 7);
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
if (lean_is_scalar(x_308)) {
 x_332 = lean_alloc_ctor(7, 2, 0);
} else {
 x_332 = x_308;
 lean_ctor_set_tag(x_332, 7);
}
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_328);
x_333 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
x_334 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
lean_inc(x_20);
x_335 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_326, x_325, x_334, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_319);
lean_dec(x_325);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
lean_dec(x_335);
x_47 = x_299;
x_48 = x_315;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_336;
goto block_61;
}
}
}
else
{
lean_dec(x_320);
lean_dec(x_316);
lean_dec(x_308);
lean_dec(x_81);
x_47 = x_299;
x_48 = x_315;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_319;
goto block_61;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
lean_dec(x_308);
x_337 = lean_ctor_get(x_313, 0);
lean_inc(x_337);
lean_dec(x_313);
x_338 = lean_ctor_get(x_311, 1);
lean_inc(x_338);
lean_dec(x_311);
x_339 = lean_ctor_get(x_312, 1);
lean_inc(x_339);
lean_dec(x_312);
x_340 = lean_ctor_get(x_337, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
lean_dec(x_337);
x_342 = lean_array_get_size(x_340);
x_343 = lean_nat_dec_lt(x_13, x_342);
lean_dec(x_342);
if (x_343 == 0)
{
lean_dec(x_340);
x_89 = x_341;
x_90 = x_299;
x_91 = x_339;
x_92 = x_15;
x_93 = x_21;
x_94 = x_14;
x_95 = x_20;
x_96 = x_16;
x_97 = x_17;
x_98 = x_18;
x_99 = x_302;
x_100 = x_19;
x_101 = x_338;
x_102 = x_306;
goto block_150;
}
else
{
lean_object* x_344; 
lean_dec(x_306);
x_344 = lean_array_fget(x_340, x_13);
lean_dec(x_340);
x_89 = x_341;
x_90 = x_299;
x_91 = x_339;
x_92 = x_15;
x_93 = x_21;
x_94 = x_14;
x_95 = x_20;
x_96 = x_16;
x_97 = x_17;
x_98 = x_18;
x_99 = x_302;
x_100 = x_19;
x_101 = x_338;
x_102 = x_344;
goto block_150;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_299);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_345 = lean_ctor_get(x_311, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_311, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_347 = x_311;
} else {
 lean_dec_ref(x_311);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_299);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_349 = lean_ctor_get(x_303, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_303, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_351 = x_303;
} else {
 lean_dec_ref(x_303);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_166);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_353 = !lean_is_exclusive(x_168);
if (x_353 == 0)
{
return x_168;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_168, 0);
x_355 = lean_ctor_get(x_168, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_168);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_357 = !lean_is_exclusive(x_165);
if (x_357 == 0)
{
return x_165;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_165, 0);
x_359 = lean_ctor_get(x_165, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_165);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
block_150:
{
lean_object* x_103; uint8_t x_104; 
x_103 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_99, x_93, x_101);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_93);
lean_inc(x_95);
lean_inc(x_100);
lean_inc(x_98);
lean_inc(x_105);
x_107 = l_Lean_MVarId_rename(x_89, x_102, x_105, x_98, x_100, x_95, x_93, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_box(0);
lean_inc(x_108);
lean_ctor_set_tag(x_103, 1);
lean_ctor_set(x_103, 1, x_110);
lean_ctor_set(x_103, 0, x_108);
x_111 = l_Lean_Elab_Tactic_setGoals___redArg(x_103, x_92, x_109);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_box(x_10);
x_114 = lean_box(x_9);
x_115 = lean_box(x_12);
lean_inc(x_108);
x_116 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_116, 0, x_108);
lean_closure_set(x_116, 1, x_105);
lean_closure_set(x_116, 2, x_113);
lean_closure_set(x_116, 3, x_114);
lean_closure_set(x_116, 4, x_81);
lean_closure_set(x_116, 5, x_88);
lean_closure_set(x_116, 6, x_11);
lean_closure_set(x_116, 7, x_79);
lean_closure_set(x_116, 8, x_115);
lean_inc(x_93);
lean_inc(x_95);
lean_inc(x_100);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_94);
x_117 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_108, x_116, x_94, x_92, x_96, x_97, x_98, x_100, x_95, x_93, x_112);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_47 = x_90;
x_48 = x_91;
x_49 = x_94;
x_50 = x_92;
x_51 = x_96;
x_52 = x_97;
x_53 = x_98;
x_54 = x_100;
x_55 = x_95;
x_56 = x_93;
x_57 = x_118;
goto block_61;
}
else
{
uint8_t x_119; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
return x_117;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_117, 0);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_117);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_103);
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_107);
if (x_123 == 0)
{
return x_107;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_107, 0);
x_125 = lean_ctor_get(x_107, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_107);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_103, 0);
x_128 = lean_ctor_get(x_103, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_103);
lean_inc(x_93);
lean_inc(x_95);
lean_inc(x_100);
lean_inc(x_98);
lean_inc(x_127);
x_129 = l_Lean_MVarId_rename(x_89, x_102, x_127, x_98, x_100, x_95, x_93, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_box(0);
lean_inc(x_130);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Elab_Tactic_setGoals___redArg(x_133, x_92, x_131);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_box(x_10);
x_137 = lean_box(x_9);
x_138 = lean_box(x_12);
lean_inc(x_130);
x_139 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_139, 0, x_130);
lean_closure_set(x_139, 1, x_127);
lean_closure_set(x_139, 2, x_136);
lean_closure_set(x_139, 3, x_137);
lean_closure_set(x_139, 4, x_81);
lean_closure_set(x_139, 5, x_88);
lean_closure_set(x_139, 6, x_11);
lean_closure_set(x_139, 7, x_79);
lean_closure_set(x_139, 8, x_138);
lean_inc(x_93);
lean_inc(x_95);
lean_inc(x_100);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_94);
x_140 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_130, x_139, x_94, x_92, x_96, x_97, x_98, x_100, x_95, x_93, x_135);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_47 = x_90;
x_48 = x_91;
x_49 = x_94;
x_50 = x_92;
x_51 = x_96;
x_52 = x_97;
x_53 = x_98;
x_54 = x_100;
x_55 = x_95;
x_56 = x_93;
x_57 = x_141;
goto block_61;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_144 = x_140;
} else {
 lean_dec_ref(x_140);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_81);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_146 = lean_ctor_get(x_129, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_129, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_148 = x_129;
} else {
 lean_dec_ref(x_129);
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
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_404; 
x_361 = lean_ctor_get(x_83, 0);
x_362 = lean_ctor_get(x_83, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_83);
x_363 = lean_ctor_get(x_84, 2);
lean_inc(x_363);
lean_dec(x_84);
x_404 = lean_unbox(x_361);
lean_dec(x_361);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_363);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_405 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3;
x_406 = l_Lean_indentExpr(x_81);
x_407 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
x_408 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5;
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_408);
lean_ctor_set(x_75, 0, x_407);
x_409 = l_Lean_Expr_mvar___override(x_2);
x_410 = l_Lean_MessageData_ofExpr(x_409);
x_411 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_411, 0, x_75);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4;
x_413 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_413, x_18, x_19, x_20, x_21, x_362);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_417 = x_414;
} else {
 lean_dec_ref(x_414);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
else
{
lean_object* x_419; 
lean_free_object(x_75);
lean_inc(x_2);
x_419 = l_Lean_MVarId_getType(x_2, x_18, x_19, x_20, x_21, x_362);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
lean_inc(x_2);
x_422 = l_Lean_MVarId_getTag(x_2, x_18, x_19, x_20, x_21, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
lean_inc(x_18);
x_425 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_420, x_423, x_18, x_19, x_20, x_21, x_424);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_428 = x_425;
} else {
 lean_dec_ref(x_425);
 x_428 = lean_box(0);
}
x_429 = l_Lean_Expr_mvarId_x21(x_426);
x_430 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_81);
x_431 = l_Lean_MVarId_note(x_429, x_430, x_81, x_79, x_18, x_19, x_20, x_21, x_427);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_436 = x_432;
} else {
 lean_dec_ref(x_432);
 x_436 = lean_box(0);
}
x_437 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_434);
x_438 = lean_array_push(x_437, x_434);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_439 = l_Lean_Meta_simpGoal(x_435, x_6, x_7, x_8, x_9, x_438, x_4, x_18, x_19, x_20, x_21, x_433);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; 
lean_dec(x_434);
lean_dec(x_363);
lean_dec(x_11);
x_442 = lean_ctor_get(x_439, 1);
lean_inc(x_442);
lean_dec(x_439);
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_444 = x_440;
} else {
 lean_dec_ref(x_440);
 x_444 = lean_box(0);
}
lean_inc(x_20);
x_445 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_442);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
x_449 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_446);
lean_dec(x_446);
if (x_449 == 0)
{
lean_dec(x_448);
lean_dec(x_444);
lean_dec(x_436);
lean_dec(x_428);
lean_dec(x_81);
x_47 = x_426;
x_48 = x_443;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_447;
goto block_61;
}
else
{
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_81, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_18, 2);
lean_inc(x_451);
x_452 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_451, x_450);
if (lean_obj_tag(x_452) == 0)
{
lean_dec(x_448);
lean_dec(x_444);
lean_dec(x_436);
lean_dec(x_428);
lean_dec(x_81);
x_47 = x_426;
x_48 = x_443;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_447;
goto block_61;
}
else
{
lean_dec(x_452);
if (x_12 == 0)
{
lean_dec(x_448);
lean_dec(x_444);
lean_dec(x_436);
lean_dec(x_428);
lean_dec(x_81);
x_47 = x_426;
x_48 = x_443;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_447;
goto block_61;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_453 = lean_ctor_get(x_20, 5);
lean_inc(x_453);
x_454 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_455 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
x_456 = l_Lean_MessageData_ofExpr(x_81);
lean_inc(x_456);
if (lean_is_scalar(x_448)) {
 x_457 = lean_alloc_ctor(7, 2, 0);
} else {
 x_457 = x_448;
 lean_ctor_set_tag(x_457, 7);
}
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
x_458 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
if (lean_is_scalar(x_444)) {
 x_459 = lean_alloc_ctor(7, 2, 0);
} else {
 x_459 = x_444;
 lean_ctor_set_tag(x_459, 7);
}
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
if (lean_is_scalar(x_436)) {
 x_460 = lean_alloc_ctor(7, 2, 0);
} else {
 x_460 = x_436;
 lean_ctor_set_tag(x_460, 7);
}
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_456);
x_461 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
if (lean_is_scalar(x_428)) {
 x_462 = lean_alloc_ctor(7, 2, 0);
} else {
 x_462 = x_428;
 lean_ctor_set_tag(x_462, 7);
}
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
lean_inc(x_20);
x_463 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_454, x_453, x_462, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_447);
lean_dec(x_453);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
lean_dec(x_463);
x_47 = x_426;
x_48 = x_443;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_464;
goto block_61;
}
}
}
else
{
lean_dec(x_448);
lean_dec(x_444);
lean_dec(x_436);
lean_dec(x_428);
lean_dec(x_81);
x_47 = x_426;
x_48 = x_443;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_447;
goto block_61;
}
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
lean_dec(x_436);
lean_dec(x_428);
x_465 = lean_ctor_get(x_441, 0);
lean_inc(x_465);
lean_dec(x_441);
x_466 = lean_ctor_get(x_439, 1);
lean_inc(x_466);
lean_dec(x_439);
x_467 = lean_ctor_get(x_440, 1);
lean_inc(x_467);
lean_dec(x_440);
x_468 = lean_ctor_get(x_465, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_465, 1);
lean_inc(x_469);
lean_dec(x_465);
x_470 = lean_array_get_size(x_468);
x_471 = lean_nat_dec_lt(x_13, x_470);
lean_dec(x_470);
if (x_471 == 0)
{
lean_dec(x_468);
x_364 = x_469;
x_365 = x_426;
x_366 = x_467;
x_367 = x_15;
x_368 = x_21;
x_369 = x_14;
x_370 = x_20;
x_371 = x_16;
x_372 = x_17;
x_373 = x_18;
x_374 = x_430;
x_375 = x_19;
x_376 = x_466;
x_377 = x_434;
goto block_403;
}
else
{
lean_object* x_472; 
lean_dec(x_434);
x_472 = lean_array_fget(x_468, x_13);
lean_dec(x_468);
x_364 = x_469;
x_365 = x_426;
x_366 = x_467;
x_367 = x_15;
x_368 = x_21;
x_369 = x_14;
x_370 = x_20;
x_371 = x_16;
x_372 = x_17;
x_373 = x_18;
x_374 = x_430;
x_375 = x_19;
x_376 = x_466;
x_377 = x_472;
goto block_403;
}
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_363);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_473 = lean_ctor_get(x_439, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_439, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_475 = x_439;
} else {
 lean_dec_ref(x_439);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
return x_476;
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_363);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_477 = lean_ctor_get(x_431, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_431, 1);
lean_inc(x_478);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_479 = x_431;
} else {
 lean_dec_ref(x_431);
 x_479 = lean_box(0);
}
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 2, 0);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_478);
return x_480;
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_420);
lean_dec(x_363);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_481 = lean_ctor_get(x_422, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_422, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_483 = x_422;
} else {
 lean_dec_ref(x_422);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
return x_484;
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_363);
lean_dec(x_81);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_485 = lean_ctor_get(x_419, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_419, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_487 = x_419;
} else {
 lean_dec_ref(x_419);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
block_403:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_378 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_374, x_368, x_376);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_381 = x_378;
} else {
 lean_dec_ref(x_378);
 x_381 = lean_box(0);
}
lean_inc(x_368);
lean_inc(x_370);
lean_inc(x_375);
lean_inc(x_373);
lean_inc(x_379);
x_382 = l_Lean_MVarId_rename(x_364, x_377, x_379, x_373, x_375, x_370, x_368, x_380);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_385 = lean_box(0);
lean_inc(x_383);
if (lean_is_scalar(x_381)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_381;
 lean_ctor_set_tag(x_386, 1);
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_Elab_Tactic_setGoals___redArg(x_386, x_367, x_384);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_box(x_10);
x_390 = lean_box(x_9);
x_391 = lean_box(x_12);
lean_inc(x_383);
x_392 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_392, 0, x_383);
lean_closure_set(x_392, 1, x_379);
lean_closure_set(x_392, 2, x_389);
lean_closure_set(x_392, 3, x_390);
lean_closure_set(x_392, 4, x_81);
lean_closure_set(x_392, 5, x_363);
lean_closure_set(x_392, 6, x_11);
lean_closure_set(x_392, 7, x_79);
lean_closure_set(x_392, 8, x_391);
lean_inc(x_368);
lean_inc(x_370);
lean_inc(x_375);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_367);
lean_inc(x_369);
x_393 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_383, x_392, x_369, x_367, x_371, x_372, x_373, x_375, x_370, x_368, x_388);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
x_47 = x_365;
x_48 = x_366;
x_49 = x_369;
x_50 = x_367;
x_51 = x_371;
x_52 = x_372;
x_53 = x_373;
x_54 = x_375;
x_55 = x_370;
x_56 = x_368;
x_57 = x_394;
goto block_61;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_375);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_3);
lean_dec(x_2);
x_395 = lean_ctor_get(x_393, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_393, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_397 = x_393;
} else {
 lean_dec_ref(x_393);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_381);
lean_dec(x_379);
lean_dec(x_375);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_81);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_399 = lean_ctor_get(x_382, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_382, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_401 = x_382;
} else {
 lean_dec_ref(x_382);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
}
}
else
{
uint8_t x_489; 
lean_free_object(x_75);
lean_dec(x_77);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_489 = !lean_is_exclusive(x_80);
if (x_489 == 0)
{
return x_80;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_80, 0);
x_491 = lean_ctor_get(x_80, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_80);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_493 = lean_ctor_get(x_75, 0);
x_494 = lean_ctor_get(x_75, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_75);
x_495 = lean_box(0);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_496 = l_Lean_Elab_Tactic_elabTerm(x_74, x_495, x_10, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_494);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_545; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
lean_inc(x_497);
x_499 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(x_2, x_497, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_498);
x_500 = lean_ctor_get(x_493, 0);
lean_inc(x_500);
lean_dec(x_493);
x_501 = lean_ctor_get(x_499, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_499, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_503 = x_499;
} else {
 lean_dec_ref(x_499);
 x_503 = lean_box(0);
}
x_504 = lean_ctor_get(x_500, 2);
lean_inc(x_504);
lean_dec(x_500);
x_545 = lean_unbox(x_501);
lean_dec(x_501);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_504);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_546 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3;
x_547 = l_Lean_indentExpr(x_497);
if (lean_is_scalar(x_503)) {
 x_548 = lean_alloc_ctor(7, 2, 0);
} else {
 x_548 = x_503;
 lean_ctor_set_tag(x_548, 7);
}
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
x_549 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5;
x_550 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
x_551 = l_Lean_Expr_mvar___override(x_2);
x_552 = l_Lean_MessageData_ofExpr(x_551);
x_553 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_552);
x_554 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4;
x_555 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
x_556 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_555, x_18, x_19, x_20, x_21, x_502);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_559 = x_556;
} else {
 lean_dec_ref(x_556);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(1, 2, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_557);
lean_ctor_set(x_560, 1, x_558);
return x_560;
}
else
{
lean_object* x_561; 
lean_dec(x_503);
lean_inc(x_2);
x_561 = l_Lean_MVarId_getType(x_2, x_18, x_19, x_20, x_21, x_502);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
lean_inc(x_2);
x_564 = l_Lean_MVarId_getTag(x_2, x_18, x_19, x_20, x_21, x_563);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
lean_inc(x_18);
x_567 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_562, x_565, x_18, x_19, x_20, x_21, x_566);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_570 = x_567;
} else {
 lean_dec_ref(x_567);
 x_570 = lean_box(0);
}
x_571 = l_Lean_Expr_mvarId_x21(x_568);
x_572 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_497);
x_573 = l_Lean_MVarId_note(x_571, x_572, x_497, x_495, x_18, x_19, x_20, x_21, x_569);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_ctor_get(x_574, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_574, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_578 = x_574;
} else {
 lean_dec_ref(x_574);
 x_578 = lean_box(0);
}
x_579 = lean_mk_empty_array_with_capacity(x_5);
lean_inc(x_576);
x_580 = lean_array_push(x_579, x_576);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_581 = l_Lean_Meta_simpGoal(x_577, x_6, x_7, x_8, x_9, x_580, x_4, x_18, x_19, x_20, x_21, x_575);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
lean_dec(x_576);
lean_dec(x_504);
lean_dec(x_11);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec(x_581);
x_585 = lean_ctor_get(x_582, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_586 = x_582;
} else {
 lean_dec_ref(x_582);
 x_586 = lean_box(0);
}
lean_inc(x_20);
x_587 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_584);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_590 = x_587;
} else {
 lean_dec_ref(x_587);
 x_590 = lean_box(0);
}
x_591 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_588);
lean_dec(x_588);
if (x_591 == 0)
{
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_578);
lean_dec(x_570);
lean_dec(x_497);
x_47 = x_568;
x_48 = x_585;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_589;
goto block_61;
}
else
{
if (lean_obj_tag(x_497) == 1)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_497, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_18, 2);
lean_inc(x_593);
x_594 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_593, x_592);
if (lean_obj_tag(x_594) == 0)
{
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_578);
lean_dec(x_570);
lean_dec(x_497);
x_47 = x_568;
x_48 = x_585;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_589;
goto block_61;
}
else
{
lean_dec(x_594);
if (x_12 == 0)
{
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_578);
lean_dec(x_570);
lean_dec(x_497);
x_47 = x_568;
x_48 = x_585;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_589;
goto block_61;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_595 = lean_ctor_get(x_20, 5);
lean_inc(x_595);
x_596 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_597 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9;
x_598 = l_Lean_MessageData_ofExpr(x_497);
lean_inc(x_598);
if (lean_is_scalar(x_590)) {
 x_599 = lean_alloc_ctor(7, 2, 0);
} else {
 x_599 = x_590;
 lean_ctor_set_tag(x_599, 7);
}
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
x_600 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11;
if (lean_is_scalar(x_586)) {
 x_601 = lean_alloc_ctor(7, 2, 0);
} else {
 x_601 = x_586;
 lean_ctor_set_tag(x_601, 7);
}
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_600);
if (lean_is_scalar(x_578)) {
 x_602 = lean_alloc_ctor(7, 2, 0);
} else {
 x_602 = x_578;
 lean_ctor_set_tag(x_602, 7);
}
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_598);
x_603 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13;
if (lean_is_scalar(x_570)) {
 x_604 = lean_alloc_ctor(7, 2, 0);
} else {
 x_604 = x_570;
 lean_ctor_set_tag(x_604, 7);
}
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
lean_inc(x_20);
x_605 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_596, x_595, x_604, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_589);
lean_dec(x_595);
x_606 = lean_ctor_get(x_605, 1);
lean_inc(x_606);
lean_dec(x_605);
x_47 = x_568;
x_48 = x_585;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_606;
goto block_61;
}
}
}
else
{
lean_dec(x_590);
lean_dec(x_586);
lean_dec(x_578);
lean_dec(x_570);
lean_dec(x_497);
x_47 = x_568;
x_48 = x_585;
x_49 = x_14;
x_50 = x_15;
x_51 = x_16;
x_52 = x_17;
x_53 = x_18;
x_54 = x_19;
x_55 = x_20;
x_56 = x_21;
x_57 = x_589;
goto block_61;
}
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; 
lean_dec(x_578);
lean_dec(x_570);
x_607 = lean_ctor_get(x_583, 0);
lean_inc(x_607);
lean_dec(x_583);
x_608 = lean_ctor_get(x_581, 1);
lean_inc(x_608);
lean_dec(x_581);
x_609 = lean_ctor_get(x_582, 1);
lean_inc(x_609);
lean_dec(x_582);
x_610 = lean_ctor_get(x_607, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_607, 1);
lean_inc(x_611);
lean_dec(x_607);
x_612 = lean_array_get_size(x_610);
x_613 = lean_nat_dec_lt(x_13, x_612);
lean_dec(x_612);
if (x_613 == 0)
{
lean_dec(x_610);
x_505 = x_611;
x_506 = x_568;
x_507 = x_609;
x_508 = x_15;
x_509 = x_21;
x_510 = x_14;
x_511 = x_20;
x_512 = x_16;
x_513 = x_17;
x_514 = x_18;
x_515 = x_572;
x_516 = x_19;
x_517 = x_608;
x_518 = x_576;
goto block_544;
}
else
{
lean_object* x_614; 
lean_dec(x_576);
x_614 = lean_array_fget(x_610, x_13);
lean_dec(x_610);
x_505 = x_611;
x_506 = x_568;
x_507 = x_609;
x_508 = x_15;
x_509 = x_21;
x_510 = x_14;
x_511 = x_20;
x_512 = x_16;
x_513 = x_17;
x_514 = x_18;
x_515 = x_572;
x_516 = x_19;
x_517 = x_608;
x_518 = x_614;
goto block_544;
}
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_578);
lean_dec(x_576);
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_615 = lean_ctor_get(x_581, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_581, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_617 = x_581;
} else {
 lean_dec_ref(x_581);
 x_617 = lean_box(0);
}
if (lean_is_scalar(x_617)) {
 x_618 = lean_alloc_ctor(1, 2, 0);
} else {
 x_618 = x_617;
}
lean_ctor_set(x_618, 0, x_615);
lean_ctor_set(x_618, 1, x_616);
return x_618;
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_619 = lean_ctor_get(x_573, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_573, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_621 = x_573;
} else {
 lean_dec_ref(x_573);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_619);
lean_ctor_set(x_622, 1, x_620);
return x_622;
}
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_562);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_623 = lean_ctor_get(x_564, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_564, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_625 = x_564;
} else {
 lean_dec_ref(x_564);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_623);
lean_ctor_set(x_626, 1, x_624);
return x_626;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_627 = lean_ctor_get(x_561, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_561, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_629 = x_561;
} else {
 lean_dec_ref(x_561);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_628);
return x_630;
}
}
block_544:
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_519 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_515, x_509, x_517);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_522 = x_519;
} else {
 lean_dec_ref(x_519);
 x_522 = lean_box(0);
}
lean_inc(x_509);
lean_inc(x_511);
lean_inc(x_516);
lean_inc(x_514);
lean_inc(x_520);
x_523 = l_Lean_MVarId_rename(x_505, x_518, x_520, x_514, x_516, x_511, x_509, x_521);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
x_526 = lean_box(0);
lean_inc(x_524);
if (lean_is_scalar(x_522)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_522;
 lean_ctor_set_tag(x_527, 1);
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_526);
x_528 = l_Lean_Elab_Tactic_setGoals___redArg(x_527, x_508, x_525);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
lean_dec(x_528);
x_530 = lean_box(x_10);
x_531 = lean_box(x_9);
x_532 = lean_box(x_12);
lean_inc(x_524);
x_533 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed), 18, 9);
lean_closure_set(x_533, 0, x_524);
lean_closure_set(x_533, 1, x_520);
lean_closure_set(x_533, 2, x_530);
lean_closure_set(x_533, 3, x_531);
lean_closure_set(x_533, 4, x_497);
lean_closure_set(x_533, 5, x_504);
lean_closure_set(x_533, 6, x_11);
lean_closure_set(x_533, 7, x_495);
lean_closure_set(x_533, 8, x_532);
lean_inc(x_509);
lean_inc(x_511);
lean_inc(x_516);
lean_inc(x_514);
lean_inc(x_513);
lean_inc(x_512);
lean_inc(x_508);
lean_inc(x_510);
x_534 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_524, x_533, x_510, x_508, x_512, x_513, x_514, x_516, x_511, x_509, x_529);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; 
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
x_47 = x_506;
x_48 = x_507;
x_49 = x_510;
x_50 = x_508;
x_51 = x_512;
x_52 = x_513;
x_53 = x_514;
x_54 = x_516;
x_55 = x_511;
x_56 = x_509;
x_57 = x_535;
goto block_61;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_516);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_3);
lean_dec(x_2);
x_536 = lean_ctor_get(x_534, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_534, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_538 = x_534;
} else {
 lean_dec_ref(x_534);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_516);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_504);
lean_dec(x_497);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_540 = lean_ctor_get(x_523, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_523, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_542 = x_523;
} else {
 lean_dec_ref(x_523);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_493);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_631 = lean_ctor_get(x_496, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_496, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_633 = x_496;
} else {
 lean_dec_ref(x_496);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_631);
lean_ctor_set(x_634, 1, x_632);
return x_634;
}
}
}
block_46:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_mk_empty_array_with_capacity(x_5);
x_25 = lean_array_push(x_24, x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_4);
x_26 = l_Lean_Meta_simpGoal(x_2, x_6, x_7, x_8, x_9, x_25, x_4, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_apply_10(x_3, x_4, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_35 = l_Lean_MVarId_assumption(x_34, x_18, x_19, x_20, x_21, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_10(x_3, x_33, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_33);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_26);
if (x_42 == 0)
{
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 0);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_26);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
block_61:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(x_2, x_47, x_54, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_apply_10(x_3, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_59);
return x_60;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try 'simp' instead of 'simpa'", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_13, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_mk_empty_array_with_capacity(x_1);
x_25 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1;
lean_inc(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
x_27 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2;
x_28 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3;
x_29 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4;
x_30 = 5;
lean_inc_n(x_1, 2);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_1);
lean_ctor_set(x_31, 3, x_1);
lean_ctor_set_usize(x_31, 4, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_31);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Meta_simpGoal(x_22, x_2, x_3, x_11, x_4, x_24, x_33, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_18);
x_38 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_40);
lean_dec(x_40);
if (x_42 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_ctor_set(x_38, 0, x_32);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_38);
x_43 = lean_ctor_get(x_18, 5);
lean_inc(x_43);
x_44 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_45 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_46 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_44, x_43, x_45, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_41);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_32);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_32);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_53 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(x_51);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_32);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_18, 5);
lean_inc(x_55);
x_56 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0;
x_57 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7;
x_58 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_56, x_55, x_57, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_52);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_55);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_32);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_32);
x_62 = lean_ctor_get(x_36, 0);
lean_inc(x_62);
lean_dec(x_36);
x_63 = lean_ctor_get(x_34, 1);
lean_inc(x_63);
lean_dec(x_34);
x_64 = lean_ctor_get(x_35, 1);
lean_inc(x_64);
lean_dec(x_35);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_box(x_8);
x_67 = lean_box(x_4);
x_68 = lean_box(x_10);
lean_inc(x_65);
x_69 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed), 22, 13);
lean_closure_set(x_69, 0, x_5);
lean_closure_set(x_69, 1, x_65);
lean_closure_set(x_69, 2, x_6);
lean_closure_set(x_69, 3, x_64);
lean_closure_set(x_69, 4, x_7);
lean_closure_set(x_69, 5, x_2);
lean_closure_set(x_69, 6, x_3);
lean_closure_set(x_69, 7, x_11);
lean_closure_set(x_69, 8, x_66);
lean_closure_set(x_69, 9, x_67);
lean_closure_set(x_69, 10, x_9);
lean_closure_set(x_69, 11, x_68);
lean_closure_set(x_69, 12, x_1);
x_70 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_65, x_69, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_63);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_34);
if (x_71 == 0)
{
return x_34;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_34, 0);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_34);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, uint8_t x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27, lean_object* x_28, lean_object* x_29, lean_object* x_30, lean_object* x_31, lean_object* x_32) {
_start:
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_st_ref_get(x_31, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_100; lean_object* x_101; lean_object* x_114; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_30, 5);
lean_inc(x_37);
x_38 = lean_box(0);
x_51 = lean_unbox(x_38);
x_52 = l_Lean_SourceInfo_fromRef(x_37, x_51);
lean_dec(x_37);
x_53 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__0;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_53);
lean_inc(x_52);
lean_ctor_set_tag(x_33, 2);
lean_ctor_set(x_33, 1, x_53);
lean_ctor_set(x_33, 0, x_52);
x_55 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__2;
x_56 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__3;
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_124; 
x_124 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_114 = x_124;
goto block_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_23, 0);
lean_inc(x_125);
lean_dec(x_23);
x_126 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_127 = lean_array_push(x_126, x_125);
x_114 = x_127;
goto block_123;
}
block_50:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_unbox(x_38);
x_45 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_43, x_44);
x_46 = lean_box(x_7);
x_47 = lean_box(x_19);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 20, 10);
lean_closure_set(x_48, 0, x_11);
lean_closure_set(x_48, 1, x_45);
lean_closure_set(x_48, 2, x_40);
lean_closure_set(x_48, 3, x_46);
lean_closure_set(x_48, 4, x_17);
lean_closure_set(x_48, 5, x_42);
lean_closure_set(x_48, 6, x_14);
lean_closure_set(x_48, 7, x_38);
lean_closure_set(x_48, 8, x_10);
lean_closure_set(x_48, 9, x_47);
x_49 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_39, x_48, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_41);
lean_dec(x_39);
return x_49;
}
block_65:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_box(x_7);
x_63 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_64 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_64, 0, x_5);
lean_closure_set(x_64, 1, x_56);
lean_closure_set(x_64, 2, x_55);
lean_closure_set(x_64, 3, x_6);
lean_closure_set(x_64, 4, x_1);
lean_closure_set(x_64, 5, x_2);
lean_closure_set(x_64, 6, x_3);
lean_closure_set(x_64, 7, x_62);
lean_closure_set(x_64, 8, x_8);
lean_closure_set(x_64, 9, x_38);
lean_closure_set(x_64, 10, x_9);
lean_closure_set(x_64, 11, x_10);
lean_closure_set(x_64, 12, x_11);
lean_closure_set(x_64, 13, x_12);
lean_closure_set(x_64, 14, x_13);
lean_closure_set(x_64, 15, x_14);
lean_closure_set(x_64, 16, x_59);
lean_closure_set(x_64, 17, x_54);
lean_closure_set(x_64, 18, x_15);
lean_closure_set(x_64, 19, x_16);
lean_closure_set(x_64, 20, x_17);
lean_closure_set(x_64, 21, x_18);
lean_closure_set(x_64, 22, x_63);
x_39 = x_58;
x_40 = x_57;
x_41 = x_61;
x_42 = x_64;
x_43 = x_60;
goto block_50;
}
block_99:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = l_Array_append___redArg(x_56, x_68);
lean_dec(x_68);
lean_inc(x_52);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_52);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_69);
lean_inc(x_52);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_55);
lean_ctor_set(x_71, 2, x_56);
lean_inc(x_54);
x_72 = l_Lean_Syntax_node6(x_52, x_54, x_33, x_4, x_66, x_67, x_70, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
lean_inc(x_72);
x_75 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_75, 0, x_72);
lean_closure_set(x_75, 1, x_38);
lean_closure_set(x_75, 2, x_73);
lean_closure_set(x_75, 3, x_38);
lean_closure_set(x_75, 4, x_74);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_76 = l_Lean_Elab_Tactic_withMainContext___redArg(x_75, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_35);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
lean_dec(x_77);
x_57 = x_80;
x_58 = x_81;
x_59 = x_72;
x_60 = x_79;
x_61 = x_78;
goto block_65;
}
else
{
if (x_19 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 2);
lean_inc(x_85);
lean_dec(x_77);
x_57 = x_84;
x_58 = x_85;
x_59 = x_72;
x_60 = x_83;
x_61 = x_82;
goto block_65;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_ctor_get(x_77, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_77, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_77, 2);
lean_inc(x_89);
lean_dec(x_77);
x_90 = lean_box(x_7);
x_91 = lean_box(x_19);
x_92 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_93 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_93, 0, x_5);
lean_closure_set(x_93, 1, x_56);
lean_closure_set(x_93, 2, x_55);
lean_closure_set(x_93, 3, x_6);
lean_closure_set(x_93, 4, x_1);
lean_closure_set(x_93, 5, x_2);
lean_closure_set(x_93, 6, x_3);
lean_closure_set(x_93, 7, x_90);
lean_closure_set(x_93, 8, x_8);
lean_closure_set(x_93, 9, x_91);
lean_closure_set(x_93, 10, x_9);
lean_closure_set(x_93, 11, x_10);
lean_closure_set(x_93, 12, x_11);
lean_closure_set(x_93, 13, x_12);
lean_closure_set(x_93, 14, x_13);
lean_closure_set(x_93, 15, x_14);
lean_closure_set(x_93, 16, x_72);
lean_closure_set(x_93, 17, x_54);
lean_closure_set(x_93, 18, x_15);
lean_closure_set(x_93, 19, x_16);
lean_closure_set(x_93, 20, x_17);
lean_closure_set(x_93, 21, x_18);
lean_closure_set(x_93, 22, x_92);
x_94 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_87);
x_39 = x_89;
x_40 = x_88;
x_41 = x_86;
x_42 = x_93;
x_43 = x_94;
goto block_50;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_72);
lean_dec(x_54);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_76);
if (x_95 == 0)
{
return x_76;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_76, 0);
x_97 = lean_ctor_get(x_76, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_76);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
block_113:
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Array_append___redArg(x_56, x_101);
lean_dec(x_101);
lean_inc(x_52);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_52);
lean_ctor_set(x_103, 1, x_55);
lean_ctor_set(x_103, 2, x_102);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_104; 
x_104 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_66 = x_100;
x_67 = x_103;
x_68 = x_104;
goto block_99;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_105 = lean_ctor_get(x_21, 0);
x_106 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3;
lean_inc(x_52);
x_107 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_107, 0, x_52);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Array_append___redArg(x_56, x_105);
lean_inc(x_52);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_52);
lean_ctor_set(x_109, 1, x_55);
lean_ctor_set(x_109, 2, x_108);
x_110 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4;
lean_inc(x_52);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_52);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Array_mkArray3___redArg(x_107, x_109, x_111);
x_66 = x_100;
x_67 = x_103;
x_68 = x_112;
goto block_99;
}
}
block_123:
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Array_append___redArg(x_56, x_114);
lean_dec(x_114);
lean_inc(x_52);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_52);
lean_ctor_set(x_116, 1, x_55);
lean_ctor_set(x_116, 2, x_115);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_117; 
x_117 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_100 = x_116;
x_101 = x_117;
goto block_113;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_22, 0);
x_119 = l_Lean_SourceInfo_fromRef(x_118, x_7);
x_120 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5;
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Array_mkArray1___redArg(x_121);
x_100 = x_116;
x_101 = x_122;
goto block_113;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_193; lean_object* x_194; lean_object* x_207; 
x_128 = lean_ctor_get(x_33, 1);
lean_inc(x_128);
lean_dec(x_33);
x_129 = lean_ctor_get(x_30, 5);
lean_inc(x_129);
x_130 = lean_box(0);
x_143 = lean_unbox(x_130);
x_144 = l_Lean_SourceInfo_fromRef(x_129, x_143);
lean_dec(x_129);
x_145 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__0;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_146 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_145);
lean_inc(x_144);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
x_148 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__2;
x_149 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__3;
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_217; 
x_217 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_207 = x_217;
goto block_216;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_23, 0);
lean_inc(x_218);
lean_dec(x_23);
x_219 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_220 = lean_array_push(x_219, x_218);
x_207 = x_220;
goto block_216;
}
block_142:
{
uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_136 = lean_unbox(x_130);
x_137 = l_Lean_Meta_Simp_Context_setFailIfUnchanged(x_135, x_136);
x_138 = lean_box(x_7);
x_139 = lean_box(x_19);
x_140 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed), 20, 10);
lean_closure_set(x_140, 0, x_11);
lean_closure_set(x_140, 1, x_137);
lean_closure_set(x_140, 2, x_132);
lean_closure_set(x_140, 3, x_138);
lean_closure_set(x_140, 4, x_17);
lean_closure_set(x_140, 5, x_134);
lean_closure_set(x_140, 6, x_14);
lean_closure_set(x_140, 7, x_130);
lean_closure_set(x_140, 8, x_10);
lean_closure_set(x_140, 9, x_139);
x_141 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_131, x_140, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_133);
lean_dec(x_131);
return x_141;
}
block_158:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_box(x_7);
x_156 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_157 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_157, 0, x_5);
lean_closure_set(x_157, 1, x_149);
lean_closure_set(x_157, 2, x_148);
lean_closure_set(x_157, 3, x_6);
lean_closure_set(x_157, 4, x_1);
lean_closure_set(x_157, 5, x_2);
lean_closure_set(x_157, 6, x_3);
lean_closure_set(x_157, 7, x_155);
lean_closure_set(x_157, 8, x_8);
lean_closure_set(x_157, 9, x_130);
lean_closure_set(x_157, 10, x_9);
lean_closure_set(x_157, 11, x_10);
lean_closure_set(x_157, 12, x_11);
lean_closure_set(x_157, 13, x_12);
lean_closure_set(x_157, 14, x_13);
lean_closure_set(x_157, 15, x_14);
lean_closure_set(x_157, 16, x_152);
lean_closure_set(x_157, 17, x_146);
lean_closure_set(x_157, 18, x_15);
lean_closure_set(x_157, 19, x_16);
lean_closure_set(x_157, 20, x_17);
lean_closure_set(x_157, 21, x_18);
lean_closure_set(x_157, 22, x_156);
x_131 = x_151;
x_132 = x_150;
x_133 = x_154;
x_134 = x_157;
x_135 = x_153;
goto block_142;
}
block_192:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = l_Array_append___redArg(x_149, x_161);
lean_dec(x_161);
lean_inc(x_144);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_144);
lean_ctor_set(x_163, 1, x_148);
lean_ctor_set(x_163, 2, x_162);
lean_inc(x_144);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_144);
lean_ctor_set(x_164, 1, x_148);
lean_ctor_set(x_164, 2, x_149);
lean_inc(x_146);
x_165 = l_Lean_Syntax_node6(x_144, x_146, x_147, x_4, x_159, x_160, x_163, x_164);
x_166 = lean_box(0);
x_167 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
lean_inc(x_165);
x_168 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_168, 0, x_165);
lean_closure_set(x_168, 1, x_130);
lean_closure_set(x_168, 2, x_166);
lean_closure_set(x_168, 3, x_130);
lean_closure_set(x_168, 4, x_167);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_169 = l_Lean_Elab_Tactic_withMainContext___redArg(x_168, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_128);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 2);
lean_inc(x_174);
lean_dec(x_170);
x_150 = x_173;
x_151 = x_174;
x_152 = x_165;
x_153 = x_172;
x_154 = x_171;
goto block_158;
}
else
{
if (x_19 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_170, 2);
lean_inc(x_178);
lean_dec(x_170);
x_150 = x_177;
x_151 = x_178;
x_152 = x_165;
x_153 = x_176;
x_154 = x_175;
goto block_158;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_179 = lean_ctor_get(x_169, 1);
lean_inc(x_179);
lean_dec(x_169);
x_180 = lean_ctor_get(x_170, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_170, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_170, 2);
lean_inc(x_182);
lean_dec(x_170);
x_183 = lean_box(x_7);
x_184 = lean_box(x_19);
x_185 = lean_box(x_19);
lean_inc(x_17);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
x_186 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed), 33, 23);
lean_closure_set(x_186, 0, x_5);
lean_closure_set(x_186, 1, x_149);
lean_closure_set(x_186, 2, x_148);
lean_closure_set(x_186, 3, x_6);
lean_closure_set(x_186, 4, x_1);
lean_closure_set(x_186, 5, x_2);
lean_closure_set(x_186, 6, x_3);
lean_closure_set(x_186, 7, x_183);
lean_closure_set(x_186, 8, x_8);
lean_closure_set(x_186, 9, x_184);
lean_closure_set(x_186, 10, x_9);
lean_closure_set(x_186, 11, x_10);
lean_closure_set(x_186, 12, x_11);
lean_closure_set(x_186, 13, x_12);
lean_closure_set(x_186, 14, x_13);
lean_closure_set(x_186, 15, x_14);
lean_closure_set(x_186, 16, x_165);
lean_closure_set(x_186, 17, x_146);
lean_closure_set(x_186, 18, x_15);
lean_closure_set(x_186, 19, x_16);
lean_closure_set(x_186, 20, x_17);
lean_closure_set(x_186, 21, x_18);
lean_closure_set(x_186, 22, x_185);
x_187 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_180);
x_131 = x_182;
x_132 = x_181;
x_133 = x_179;
x_134 = x_186;
x_135 = x_187;
goto block_142;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_165);
lean_dec(x_146);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_169, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_169, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_190 = x_169;
} else {
 lean_dec_ref(x_169);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
block_206:
{
lean_object* x_195; lean_object* x_196; 
x_195 = l_Array_append___redArg(x_149, x_194);
lean_dec(x_194);
lean_inc(x_144);
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_144);
lean_ctor_set(x_196, 1, x_148);
lean_ctor_set(x_196, 2, x_195);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_197; 
x_197 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_159 = x_193;
x_160 = x_196;
x_161 = x_197;
goto block_192;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_198 = lean_ctor_get(x_21, 0);
x_199 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3;
lean_inc(x_144);
x_200 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_200, 0, x_144);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Array_append___redArg(x_149, x_198);
lean_inc(x_144);
x_202 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_202, 0, x_144);
lean_ctor_set(x_202, 1, x_148);
lean_ctor_set(x_202, 2, x_201);
x_203 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4;
lean_inc(x_144);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_144);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Array_mkArray3___redArg(x_200, x_202, x_204);
x_159 = x_193;
x_160 = x_196;
x_161 = x_205;
goto block_192;
}
}
block_216:
{
lean_object* x_208; lean_object* x_209; 
x_208 = l_Array_append___redArg(x_149, x_207);
lean_dec(x_207);
lean_inc(x_144);
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_144);
lean_ctor_set(x_209, 1, x_148);
lean_ctor_set(x_209, 2, x_208);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_210; 
x_210 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0;
x_193 = x_209;
x_194 = x_210;
goto block_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_22, 0);
x_212 = l_Lean_SourceInfo_fromRef(x_211, x_7);
x_213 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5;
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Array_mkArray1___redArg(x_214);
x_193 = x_209;
x_194 = x_215;
goto block_206;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpa", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpaArgsRest", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_12 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_13 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_14 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3;
x_15 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4;
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_193; uint8_t x_194; 
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed), 9, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_193 = l_Lean_Syntax_getArg(x_1, x_21);
x_194 = l_Lean_Syntax_isNone(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_inc(x_193);
x_195 = l_Lean_Syntax_matchesNull(x_193, x_21);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_193);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Lean_Syntax_getArg(x_193, x_19);
lean_dec(x_193);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_174 = x_198;
x_175 = x_2;
x_176 = x_3;
x_177 = x_4;
x_178 = x_5;
x_179 = x_6;
x_180 = x_7;
x_181 = x_8;
x_182 = x_9;
x_183 = x_10;
goto block_192;
}
}
else
{
lean_object* x_199; 
lean_dec(x_193);
x_199 = lean_box(0);
x_174 = x_199;
x_175 = x_2;
x_176 = x_3;
x_177 = x_4;
x_178 = x_5;
x_179 = x_6;
x_180 = x_7;
x_181 = x_8;
x_182 = x_9;
x_183 = x_10;
goto block_192;
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_box(x_16);
x_45 = lean_box(x_32);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___boxed), 32, 23);
lean_closure_set(x_46, 0, x_11);
lean_closure_set(x_46, 1, x_12);
lean_closure_set(x_46, 2, x_13);
lean_closure_set(x_46, 3, x_31);
lean_closure_set(x_46, 4, x_20);
lean_closure_set(x_46, 5, x_38);
lean_closure_set(x_46, 6, x_44);
lean_closure_set(x_46, 7, x_15);
lean_closure_set(x_46, 8, x_18);
lean_closure_set(x_46, 9, x_14);
lean_closure_set(x_46, 10, x_19);
lean_closure_set(x_46, 11, x_36);
lean_closure_set(x_46, 12, x_41);
lean_closure_set(x_46, 13, x_21);
lean_closure_set(x_46, 14, x_29);
lean_closure_set(x_46, 15, x_42);
lean_closure_set(x_46, 16, x_35);
lean_closure_set(x_46, 17, x_34);
lean_closure_set(x_46, 18, x_45);
lean_closure_set(x_46, 19, x_39);
lean_closure_set(x_46, 20, x_30);
lean_closure_set(x_46, 21, x_23);
lean_closure_set(x_46, 22, x_43);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = l_Lean_Elab_Tactic_focus___redArg(x_47, x_22, x_28, x_27, x_33, x_26, x_40, x_25, x_24, x_37);
return x_48;
}
block_77:
{
lean_object* x_72; 
x_72 = l_Lean_Syntax_getOptional_x3f(x_67);
lean_dec(x_67);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_box(0);
x_22 = x_50;
x_23 = x_51;
x_24 = x_52;
x_25 = x_53;
x_26 = x_54;
x_27 = x_55;
x_28 = x_56;
x_29 = x_57;
x_30 = x_58;
x_31 = x_59;
x_32 = x_60;
x_33 = x_61;
x_34 = x_62;
x_35 = x_71;
x_36 = x_63;
x_37 = x_66;
x_38 = x_65;
x_39 = x_64;
x_40 = x_68;
x_41 = x_69;
x_42 = x_70;
x_43 = x_73;
goto block_49;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
x_22 = x_50;
x_23 = x_51;
x_24 = x_52;
x_25 = x_53;
x_26 = x_54;
x_27 = x_55;
x_28 = x_56;
x_29 = x_57;
x_30 = x_58;
x_31 = x_59;
x_32 = x_60;
x_33 = x_61;
x_34 = x_62;
x_35 = x_71;
x_36 = x_63;
x_37 = x_66;
x_38 = x_65;
x_39 = x_64;
x_40 = x_68;
x_41 = x_69;
x_42 = x_70;
x_43 = x_72;
goto block_49;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_22 = x_50;
x_23 = x_51;
x_24 = x_52;
x_25 = x_53;
x_26 = x_54;
x_27 = x_55;
x_28 = x_56;
x_29 = x_57;
x_30 = x_58;
x_31 = x_59;
x_32 = x_60;
x_33 = x_61;
x_34 = x_62;
x_35 = x_71;
x_36 = x_63;
x_37 = x_66;
x_38 = x_65;
x_39 = x_64;
x_40 = x_68;
x_41 = x_69;
x_42 = x_70;
x_43 = x_76;
goto block_49;
}
}
}
block_108:
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_unsigned_to_nat(4u);
x_101 = l_Lean_Syntax_getArg(x_78, x_100);
lean_dec(x_78);
x_102 = l_Lean_Syntax_isNone(x_101);
if (x_102 == 0)
{
uint8_t x_103; 
lean_inc(x_101);
x_103 = l_Lean_Syntax_matchesNull(x_101, x_91);
lean_dec(x_91);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_20);
lean_dec(x_18);
x_104 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_92);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_Syntax_getArg(x_101, x_21);
lean_dec(x_101);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_50 = x_79;
x_51 = x_80;
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_99;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_100;
x_64 = x_94;
x_65 = x_93;
x_66 = x_92;
x_67 = x_96;
x_68 = x_95;
x_69 = x_97;
x_70 = x_98;
x_71 = x_106;
goto block_77;
}
}
else
{
lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_91);
x_107 = lean_box(0);
x_50 = x_79;
x_51 = x_80;
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_99;
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_100;
x_64 = x_94;
x_65 = x_93;
x_66 = x_92;
x_67 = x_96;
x_68 = x_95;
x_69 = x_97;
x_70 = x_98;
x_71 = x_107;
goto block_77;
}
}
block_143:
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Syntax_getArg(x_117, x_119);
lean_dec(x_119);
x_132 = l_Lean_Syntax_isNone(x_131);
if (x_132 == 0)
{
uint8_t x_133; 
lean_inc(x_131);
x_133 = l_Lean_Syntax_matchesNull(x_131, x_21);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_20);
lean_dec(x_18);
x_134 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_130);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = l_Lean_Syntax_getArg(x_131, x_19);
lean_dec(x_131);
x_136 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5;
lean_inc(x_135);
x_137 = l_Lean_Syntax_isOfKind(x_135, x_136);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_20);
lean_dec(x_18);
x_138 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_130);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = l_Lean_Syntax_getArg(x_135, x_21);
lean_dec(x_135);
x_140 = l_Lean_Syntax_getArgs(x_139);
lean_dec(x_139);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_78 = x_117;
x_79 = x_122;
x_80 = x_121;
x_81 = x_129;
x_82 = x_128;
x_83 = x_126;
x_84 = x_124;
x_85 = x_123;
x_86 = x_116;
x_87 = x_109;
x_88 = x_110;
x_89 = x_125;
x_90 = x_111;
x_91 = x_120;
x_92 = x_130;
x_93 = x_113;
x_94 = x_112;
x_95 = x_127;
x_96 = x_118;
x_97 = x_114;
x_98 = x_115;
x_99 = x_141;
goto block_108;
}
}
}
else
{
lean_object* x_142; 
lean_dec(x_131);
x_142 = lean_box(0);
x_78 = x_117;
x_79 = x_122;
x_80 = x_121;
x_81 = x_129;
x_82 = x_128;
x_83 = x_126;
x_84 = x_124;
x_85 = x_123;
x_86 = x_116;
x_87 = x_109;
x_88 = x_110;
x_89 = x_125;
x_90 = x_111;
x_91 = x_120;
x_92 = x_130;
x_93 = x_113;
x_94 = x_112;
x_95 = x_127;
x_96 = x_118;
x_97 = x_114;
x_98 = x_115;
x_99 = x_142;
goto block_108;
}
}
block_173:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_unsigned_to_nat(3u);
x_157 = l_Lean_Syntax_getArg(x_1, x_156);
lean_dec(x_1);
x_158 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7;
lean_inc(x_157);
x_159 = l_Lean_Syntax_isOfKind(x_157, x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_18);
x_160 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_148);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = l_Lean_Syntax_getArg(x_157, x_19);
x_162 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9;
lean_inc(x_161);
x_163 = l_Lean_Syntax_isOfKind(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_161);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_18);
x_164 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_148);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = l_Lean_Syntax_getArg(x_157, x_21);
x_166 = l_Lean_Syntax_getArg(x_157, x_154);
x_167 = l_Lean_Syntax_isNone(x_166);
if (x_167 == 0)
{
uint8_t x_168; 
lean_inc(x_166);
x_168 = l_Lean_Syntax_matchesNull(x_166, x_21);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_161);
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_18);
x_169 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_148);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = l_Lean_Syntax_getArg(x_166, x_19);
lean_dec(x_166);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
lean_inc(x_154);
x_109 = x_161;
x_110 = x_163;
x_111 = x_149;
x_112 = x_155;
x_113 = x_158;
x_114 = x_156;
x_115 = x_154;
x_116 = x_162;
x_117 = x_157;
x_118 = x_165;
x_119 = x_156;
x_120 = x_154;
x_121 = x_171;
x_122 = x_151;
x_123 = x_145;
x_124 = x_144;
x_125 = x_150;
x_126 = x_153;
x_127 = x_147;
x_128 = x_152;
x_129 = x_146;
x_130 = x_148;
goto block_143;
}
}
else
{
lean_object* x_172; 
lean_dec(x_166);
x_172 = lean_box(0);
lean_inc(x_154);
x_109 = x_161;
x_110 = x_163;
x_111 = x_149;
x_112 = x_155;
x_113 = x_158;
x_114 = x_156;
x_115 = x_154;
x_116 = x_162;
x_117 = x_157;
x_118 = x_165;
x_119 = x_156;
x_120 = x_154;
x_121 = x_172;
x_122 = x_151;
x_123 = x_145;
x_124 = x_144;
x_125 = x_150;
x_126 = x_153;
x_127 = x_147;
x_128 = x_152;
x_129 = x_146;
x_130 = x_148;
goto block_143;
}
}
}
}
block_192:
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_unsigned_to_nat(2u);
x_185 = l_Lean_Syntax_getArg(x_1, x_184);
x_186 = l_Lean_Syntax_isNone(x_185);
if (x_186 == 0)
{
uint8_t x_187; 
lean_inc(x_185);
x_187 = l_Lean_Syntax_matchesNull(x_185, x_21);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_185);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
x_188 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_183);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = l_Lean_Syntax_getArg(x_185, x_19);
lean_dec(x_185);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_144 = x_177;
x_145 = x_176;
x_146 = x_182;
x_147 = x_180;
x_148 = x_183;
x_149 = x_174;
x_150 = x_178;
x_151 = x_175;
x_152 = x_181;
x_153 = x_179;
x_154 = x_184;
x_155 = x_190;
goto block_173;
}
}
else
{
lean_object* x_191; 
lean_dec(x_185);
x_191 = lean_box(0);
x_144 = x_177;
x_145 = x_176;
x_146 = x_182;
x_147 = x_180;
x_148 = x_183;
x_149 = x_174;
x_150 = x_178;
x_151 = x_175;
x_152 = x_181;
x_153 = x_179;
x_154 = x_184;
x_155 = x_191;
goto block_173;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_logWarningAt___at___Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___boxed(lean_object** _args) {
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
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
lean_object* x_33 = _args[32];
_start:
{
uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_34 = lean_unbox(x_8);
lean_dec(x_8);
x_35 = lean_unbox(x_10);
lean_dec(x_10);
x_36 = lean_unbox(x_23);
lean_dec(x_23);
x_37 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_34, x_9, x_35, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_36, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = lean_unbox(x_9);
lean_dec(x_9);
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4(x_1, x_2, x_19, x_20, x_5, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___boxed(lean_object** _args) {
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
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_unbox(x_9);
lean_dec(x_9);
x_24 = lean_unbox(x_10);
lean_dec(x_10);
x_25 = lean_unbox(x_12);
lean_dec(x_12);
x_26 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_24, x_11, x_25, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_13);
lean_dec(x_5);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___boxed(lean_object** _args) {
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
uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_unbox(x_4);
lean_dec(x_4);
x_22 = lean_unbox(x_8);
lean_dec(x_8);
x_23 = lean_unbox(x_10);
lean_dec(x_10);
x_24 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6(x_1, x_2, x_3, x_21, x_5, x_6, x_7, x_22, x_9, x_23, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___boxed(lean_object** _args) {
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
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
lean_object* x_28 = _args[27];
lean_object* x_29 = _args[28];
lean_object* x_30 = _args[29];
lean_object* x_31 = _args[30];
lean_object* x_32 = _args[31];
_start:
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_unbox(x_7);
lean_dec(x_7);
x_34 = lean_unbox(x_19);
lean_dec(x_19);
x_35 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_34, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
return x_35;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simpa", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpa", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1;
x_5 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = lean_unsigned_to_nat(90u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(43u);
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(47u);
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_App(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simpa(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_initFn___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_4_ = _init_l_initFn___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_4_();
lean_mark_persistent(l_initFn___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_4_);
l_initFn___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_4_ = _init_l_initFn___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_4_();
lean_mark_persistent(l_initFn___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_4_);
l_initFn___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_4_ = _init_l_initFn___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_4_();
lean_mark_persistent(l_initFn___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_4_);
l_initFn___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_4_ = _init_l_initFn___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_4_();
lean_mark_persistent(l_initFn___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_4_);
l_initFn___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_4_ = _init_l_initFn___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_4_();
lean_mark_persistent(l_initFn___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_4_);
l_initFn___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_4_ = _init_l_initFn___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_4_();
lean_mark_persistent(l_initFn___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_4_);
res = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_linter_unnecessarySimpa = lean_io_result_get_value(res);
lean_mark_persistent(l_linter_unnecessarySimpa);
lean_dec_ref(res);
l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__0);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__0____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__1____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__2____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__3____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__4____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__5____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__6____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__6____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__6____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__7____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__7____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__7____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__8____x40_Lean_Elab_Tactic_Simpa___hyg_51_ = _init_l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__8____x40_Lean_Elab_Tactic_Simpa___hyg_51_();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult___closed__8____x40_Lean_Elab_Tactic_Simpa___hyg_51_);
l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__0);
l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult = _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult);
l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___closed__0 = _init_l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__0___closed__0);
l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0 = _init_l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Options_toLinterOptions___at___Lean_Linter_getLinterOptions___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__1_spec__1___redArg___closed__0);
l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0 = _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__0);
l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1 = _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__1);
l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2 = _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__2);
l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3 = _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__3);
l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4 = _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__4);
l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__5 = _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__5();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__5);
l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__6 = _init_l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__6();
lean_mark_persistent(l_Lean_Linter_logLint___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__3___closed__6);
l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0 = _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__0);
l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__1 = _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__1();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5_spec__5_spec__5___closed__1);
l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__0 = _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__0();
lean_mark_persistent(l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__0);
l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__1 = _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__1();
lean_mark_persistent(l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__1);
l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__2 = _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__2();
lean_mark_persistent(l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__2);
l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__3 = _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__3();
lean_mark_persistent(l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__3);
l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__4 = _init_l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__4();
lean_mark_persistent(l_Lean_occursCheck___at___Lean_Elab_Tactic_Simpa_evalSimpa_spec__5___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__2___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__9 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__9);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__10 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__10);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__11);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__12 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__3___closed__12);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__4___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__9);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__10 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__10);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__11);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__12 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__12);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__5___closed__13);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__6___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lam__7___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__9);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4);
if (builtin) {res = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
