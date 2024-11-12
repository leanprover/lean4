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
LEAN_EXPORT lean_object* l_linter_unnecessarySimpa;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__10;
static lean_object* l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__1;
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__8;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__9;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__5;
extern lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__10;
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__14;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__3;
lean_object* l_Lean_LocalContext_getRoundtrippingUserName_x3f(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__6;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__17;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__1;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__14___boxed(lean_object**);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___boxed(lean_object**);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__13;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4;
static lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__5___boxed(lean_object**);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1(lean_object*);
static lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__3;
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___boxed(lean_object**);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_note(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__2;
static lean_object* l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__3;
lean_object* l_Lean_Elab_Tactic_instInhabitedTacticM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__20;
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__16;
static lean_object* l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___boxed(lean_object**);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__5;
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__18;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__2;
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4;
static lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___boxed(lean_object**);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__3;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___boxed(lean_object**);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3;
static lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__16___boxed(lean_object**);
lean_object* l_Lean_Elab_Tactic_closeMainGoal(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__5;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__4;
lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3025_(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__10;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21;
static lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__3;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__12;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__15;
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__11;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__1;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_object* l_Array_mkArray1___rarg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__1;
static lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__6;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__4;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__15;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__4;
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___boxed(lean_object**);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__3;
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__1;
static lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__7;
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__2;
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
static lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__7;
static lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__6;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2___closed__1;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__17;
static lean_object* _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("linter", 6, 6);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unnecessarySimpa", 16, 16);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__1;
x_2 = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("enable the 'unnecessary simpa' linter", 37, 37);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__4;
x_3 = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__3;
x_3 = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__6;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(x_2, x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1() {
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
x_2 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.no", 41, 41);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3;
x_2 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6;
x_2 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.yes", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__10;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.UseImplicitLambdaResult.postpone", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3;
x_2 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__13;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__15() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__14;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6;
x_2 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__13;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__16;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = lean_nat_dec_le(x_10, x_2);
x_12 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3025_(x_9, x_10);
x_13 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__11;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
if (x_11 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = 0;
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = 0;
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
}
default: 
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(1024u);
x_26 = lean_nat_dec_le(x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__15;
x_28 = l_Repr_addAppParen(x_27, x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__17;
x_30 = l_Repr_addAppParen(x_29, x_2);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("note: this linter can be disabled with `set_option ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" false`", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
lean_inc(x_14);
x_16 = l_Lean_MessageData_ofName(x_14);
x_17 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__2;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_17);
x_18 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
x_22 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__7;
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
x_27 = 1;
x_28 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_2, x_26, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
lean_inc(x_29);
x_30 = l_Lean_MessageData_ofName(x_29);
x_31 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__2;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_37 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__7;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_40);
x_42 = 1;
x_43 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_2, x_41, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_43;
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instInhabitedTacticM___boxed), 9, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2___closed__1;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_8, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_15, x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_12, 0, x_18);
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
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_21, x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_8, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_15, x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_12, 0, x_18);
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
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_21, x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_name_eq(x_1, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_20 = l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__7(x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_2);
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
x_28 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
lean_ctor_set(x_21, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
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
x_35 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
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
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_ctor_get(x_23, 0);
lean_inc(x_40);
lean_dec(x_23);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_2 = x_41;
x_3 = x_39;
x_12 = x_38;
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
x_46 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_45, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_47 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Expr_hasExprMVar(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = l_Lean_Expr_hash(x_2);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_18, x_31);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(x_2, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_35 = lean_ctor_get(x_3, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_dec(x_36);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_17, x_37);
lean_dec(x_17);
x_39 = lean_box(0);
lean_inc(x_2);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_32);
x_41 = lean_array_uset(x_18, x_31, x_40);
x_42 = lean_unsigned_to_nat(4u);
x_43 = lean_nat_mul(x_38, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(x_41);
lean_ctor_set(x_3, 1, x_48);
lean_ctor_set(x_3, 0, x_38);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5(x_1, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_50;
}
case 5:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_dec(x_2);
x_53 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_52);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_53, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_54, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_54, 0, x_62);
return x_53;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_dec(x_54);
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_53, 0, x_67);
return x_53;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_dec(x_53);
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_70 = x_54;
} else {
 lean_dec_ref(x_54);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_55, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_72 = x_55;
} else {
 lean_dec_ref(x_55);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_55);
x_76 = lean_ctor_get(x_53, 1);
lean_inc(x_76);
lean_dec(x_53);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
lean_dec(x_54);
x_2 = x_52;
x_3 = x_77;
x_12 = x_76;
goto _start;
}
}
case 6:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 2);
lean_inc(x_80);
lean_dec(x_2);
x_81 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_80);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_81, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_82, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_81;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_82, 0, x_90);
return x_81;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_92 = lean_ctor_get(x_83, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
lean_ctor_set(x_81, 0, x_95);
return x_81;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
lean_dec(x_81);
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_98 = x_82;
} else {
 lean_dec_ref(x_82);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_100 = x_83;
} else {
 lean_dec_ref(x_83);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
if (lean_is_scalar(x_98)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_98;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_97);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_96);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_83);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
lean_dec(x_81);
x_105 = lean_ctor_get(x_82, 1);
lean_inc(x_105);
lean_dec(x_82);
x_2 = x_80;
x_3 = x_105;
x_12 = x_104;
goto _start;
}
}
case 7:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_2, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 2);
lean_inc(x_108);
lean_dec(x_2);
x_109 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_107, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_108);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_109, 0);
lean_dec(x_113);
x_114 = !lean_is_exclusive(x_110);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_110, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_111);
if (x_116 == 0)
{
return x_109;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
lean_dec(x_111);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_110, 0, x_118);
return x_109;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_110, 1);
lean_inc(x_119);
lean_dec(x_110);
x_120 = lean_ctor_get(x_111, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_ctor_get(x_109, 1);
lean_inc(x_124);
lean_dec(x_109);
x_125 = lean_ctor_get(x_110, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_126 = x_110;
} else {
 lean_dec_ref(x_110);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_111, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_128 = x_111;
} else {
 lean_dec_ref(x_111);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 1, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_127);
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_124);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_111);
x_132 = lean_ctor_get(x_109, 1);
lean_inc(x_132);
lean_dec(x_109);
x_133 = lean_ctor_get(x_110, 1);
lean_inc(x_133);
lean_dec(x_110);
x_2 = x_108;
x_3 = x_133;
x_12 = x_132;
goto _start;
}
}
case 8:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_2, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 3);
lean_inc(x_137);
lean_dec(x_2);
x_138 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
lean_dec(x_137);
lean_dec(x_136);
x_141 = !lean_is_exclusive(x_138);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_138, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_139);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_139, 0);
lean_dec(x_144);
x_145 = !lean_is_exclusive(x_140);
if (x_145 == 0)
{
return x_138;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
lean_dec(x_140);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_139, 0, x_147);
return x_138;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_139, 1);
lean_inc(x_148);
lean_dec(x_139);
x_149 = lean_ctor_get(x_140, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_150 = x_140;
} else {
 lean_dec_ref(x_140);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_148);
lean_ctor_set(x_138, 0, x_152);
return x_138;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_138, 1);
lean_inc(x_153);
lean_dec(x_138);
x_154 = lean_ctor_get(x_139, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_155 = x_139;
} else {
 lean_dec_ref(x_139);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_140, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_157 = x_140;
} else {
 lean_dec_ref(x_140);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
if (lean_is_scalar(x_155)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_155;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_154);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_153);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_140);
x_161 = lean_ctor_get(x_138, 1);
lean_inc(x_161);
lean_dec(x_138);
x_162 = lean_ctor_get(x_139, 1);
lean_inc(x_162);
lean_dec(x_139);
x_163 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_136, x_162, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_161);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
lean_dec(x_137);
x_166 = !lean_is_exclusive(x_163);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_ctor_get(x_163, 0);
lean_dec(x_167);
x_168 = !lean_is_exclusive(x_164);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = lean_ctor_get(x_164, 0);
lean_dec(x_169);
x_170 = !lean_is_exclusive(x_165);
if (x_170 == 0)
{
return x_163;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_165, 0);
lean_inc(x_171);
lean_dec(x_165);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_164, 0, x_172);
return x_163;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_164, 1);
lean_inc(x_173);
lean_dec(x_164);
x_174 = lean_ctor_get(x_165, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_175 = x_165;
} else {
 lean_dec_ref(x_165);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_173);
lean_ctor_set(x_163, 0, x_177);
return x_163;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_178 = lean_ctor_get(x_163, 1);
lean_inc(x_178);
lean_dec(x_163);
x_179 = lean_ctor_get(x_164, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_180 = x_164;
} else {
 lean_dec_ref(x_164);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_165, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_182 = x_165;
} else {
 lean_dec_ref(x_165);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 1, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_181);
if (lean_is_scalar(x_180)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_180;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_179);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_178);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_165);
x_186 = lean_ctor_get(x_163, 1);
lean_inc(x_186);
lean_dec(x_163);
x_187 = lean_ctor_get(x_164, 1);
lean_inc(x_187);
lean_dec(x_164);
x_2 = x_137;
x_3 = x_187;
x_12 = x_186;
goto _start;
}
}
}
case 10:
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_2, 1);
lean_inc(x_189);
lean_dec(x_2);
x_2 = x_189;
goto _start;
}
case 11:
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_2, 2);
lean_inc(x_191);
lean_dec(x_2);
x_2 = x_191;
goto _start;
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_2);
x_193 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_3);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_12);
return x_195;
}
}
}
else
{
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_38);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_2, 0);
lean_inc(x_196);
lean_dec(x_2);
x_197 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5(x_1, x_196, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_197;
}
case 5:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_2, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_2, 1);
lean_inc(x_199);
lean_dec(x_2);
x_200 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_198, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
lean_dec(x_199);
x_203 = !lean_is_exclusive(x_200);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_200, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_201);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = lean_ctor_get(x_201, 0);
lean_dec(x_206);
x_207 = !lean_is_exclusive(x_202);
if (x_207 == 0)
{
return x_200;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
lean_dec(x_202);
x_209 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_201, 0, x_209);
return x_200;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_201, 1);
lean_inc(x_210);
lean_dec(x_201);
x_211 = lean_ctor_get(x_202, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_212 = x_202;
} else {
 lean_dec_ref(x_202);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_210);
lean_ctor_set(x_200, 0, x_214);
return x_200;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_215 = lean_ctor_get(x_200, 1);
lean_inc(x_215);
lean_dec(x_200);
x_216 = lean_ctor_get(x_201, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_217 = x_201;
} else {
 lean_dec_ref(x_201);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_202, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_219 = x_202;
} else {
 lean_dec_ref(x_202);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 1, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_218);
if (lean_is_scalar(x_217)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_217;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_216);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_215);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_202);
x_223 = lean_ctor_get(x_200, 1);
lean_inc(x_223);
lean_dec(x_200);
x_224 = lean_ctor_get(x_201, 1);
lean_inc(x_224);
lean_dec(x_201);
x_2 = x_199;
x_3 = x_224;
x_12 = x_223;
goto _start;
}
}
case 6:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_2, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_2, 2);
lean_inc(x_227);
lean_dec(x_2);
x_228 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_226, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
uint8_t x_231; 
lean_dec(x_227);
x_231 = !lean_is_exclusive(x_228);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_228, 0);
lean_dec(x_232);
x_233 = !lean_is_exclusive(x_229);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_229, 0);
lean_dec(x_234);
x_235 = !lean_is_exclusive(x_230);
if (x_235 == 0)
{
return x_228;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_230, 0);
lean_inc(x_236);
lean_dec(x_230);
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_229, 0, x_237);
return x_228;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_229, 1);
lean_inc(x_238);
lean_dec(x_229);
x_239 = lean_ctor_get(x_230, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_240 = x_230;
} else {
 lean_dec_ref(x_230);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(0, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_238);
lean_ctor_set(x_228, 0, x_242);
return x_228;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_228, 1);
lean_inc(x_243);
lean_dec(x_228);
x_244 = lean_ctor_get(x_229, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_245 = x_229;
} else {
 lean_dec_ref(x_229);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_230, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_247 = x_230;
} else {
 lean_dec_ref(x_230);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 1, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
if (lean_is_scalar(x_245)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_245;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_244);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_243);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_230);
x_251 = lean_ctor_get(x_228, 1);
lean_inc(x_251);
lean_dec(x_228);
x_252 = lean_ctor_get(x_229, 1);
lean_inc(x_252);
lean_dec(x_229);
x_2 = x_227;
x_3 = x_252;
x_12 = x_251;
goto _start;
}
}
case 7:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_2, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_2, 2);
lean_inc(x_255);
lean_dec(x_2);
x_256 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_254, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
lean_dec(x_255);
x_259 = !lean_is_exclusive(x_256);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_256, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_257);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_257, 0);
lean_dec(x_262);
x_263 = !lean_is_exclusive(x_258);
if (x_263 == 0)
{
return x_256;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_258, 0);
lean_inc(x_264);
lean_dec(x_258);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_257, 0, x_265);
return x_256;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_257, 1);
lean_inc(x_266);
lean_dec(x_257);
x_267 = lean_ctor_get(x_258, 0);
lean_inc(x_267);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_268 = x_258;
} else {
 lean_dec_ref(x_258);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 1, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_267);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set(x_256, 0, x_270);
return x_256;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_271 = lean_ctor_get(x_256, 1);
lean_inc(x_271);
lean_dec(x_256);
x_272 = lean_ctor_get(x_257, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_273 = x_257;
} else {
 lean_dec_ref(x_257);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_258, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_275 = x_258;
} else {
 lean_dec_ref(x_258);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_274);
if (lean_is_scalar(x_273)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_273;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_272);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_271);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_258);
x_279 = lean_ctor_get(x_256, 1);
lean_inc(x_279);
lean_dec(x_256);
x_280 = lean_ctor_get(x_257, 1);
lean_inc(x_280);
lean_dec(x_257);
x_2 = x_255;
x_3 = x_280;
x_12 = x_279;
goto _start;
}
}
case 8:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_2, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_2, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_2, 3);
lean_inc(x_284);
lean_dec(x_2);
x_285 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_282, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
lean_dec(x_284);
lean_dec(x_283);
x_288 = !lean_is_exclusive(x_285);
if (x_288 == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_285, 0);
lean_dec(x_289);
x_290 = !lean_is_exclusive(x_286);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
x_291 = lean_ctor_get(x_286, 0);
lean_dec(x_291);
x_292 = !lean_is_exclusive(x_287);
if (x_292 == 0)
{
return x_285;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_287, 0);
lean_inc(x_293);
lean_dec(x_287);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_286, 0, x_294);
return x_285;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_295 = lean_ctor_get(x_286, 1);
lean_inc(x_295);
lean_dec(x_286);
x_296 = lean_ctor_get(x_287, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_297 = x_287;
} else {
 lean_dec_ref(x_287);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_296);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_295);
lean_ctor_set(x_285, 0, x_299);
return x_285;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_300 = lean_ctor_get(x_285, 1);
lean_inc(x_300);
lean_dec(x_285);
x_301 = lean_ctor_get(x_286, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_302 = x_286;
} else {
 lean_dec_ref(x_286);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_287, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 x_304 = x_287;
} else {
 lean_dec_ref(x_287);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 1, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_303);
if (lean_is_scalar(x_302)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_302;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_301);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_300);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_287);
x_308 = lean_ctor_get(x_285, 1);
lean_inc(x_308);
lean_dec(x_285);
x_309 = lean_ctor_get(x_286, 1);
lean_inc(x_309);
lean_dec(x_286);
x_310 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_283, x_309, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_308);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_313; 
lean_dec(x_284);
x_313 = !lean_is_exclusive(x_310);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_310, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_311);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_311, 0);
lean_dec(x_316);
x_317 = !lean_is_exclusive(x_312);
if (x_317 == 0)
{
return x_310;
}
else
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_312, 0);
lean_inc(x_318);
lean_dec(x_312);
x_319 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_311, 0, x_319);
return x_310;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_320 = lean_ctor_get(x_311, 1);
lean_inc(x_320);
lean_dec(x_311);
x_321 = lean_ctor_get(x_312, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 x_322 = x_312;
} else {
 lean_dec_ref(x_312);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 1, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_321);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_320);
lean_ctor_set(x_310, 0, x_324);
return x_310;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_325 = lean_ctor_get(x_310, 1);
lean_inc(x_325);
lean_dec(x_310);
x_326 = lean_ctor_get(x_311, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_327 = x_311;
} else {
 lean_dec_ref(x_311);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get(x_312, 0);
lean_inc(x_328);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 x_329 = x_312;
} else {
 lean_dec_ref(x_312);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 1, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_328);
if (lean_is_scalar(x_327)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_327;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_326);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_325);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_312);
x_333 = lean_ctor_get(x_310, 1);
lean_inc(x_333);
lean_dec(x_310);
x_334 = lean_ctor_get(x_311, 1);
lean_inc(x_334);
lean_dec(x_311);
x_2 = x_284;
x_3 = x_334;
x_12 = x_333;
goto _start;
}
}
}
case 10:
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_2, 1);
lean_inc(x_336);
lean_dec(x_2);
x_2 = x_336;
goto _start;
}
case 11:
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_2, 2);
lean_inc(x_338);
lean_dec(x_2);
x_2 = x_338;
goto _start;
}
default: 
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_2);
x_340 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_3);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_12);
return x_342;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
lean_dec(x_3);
x_343 = lean_unsigned_to_nat(1u);
x_344 = lean_nat_add(x_17, x_343);
lean_dec(x_17);
x_345 = lean_box(0);
lean_inc(x_2);
x_346 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_346, 0, x_2);
lean_ctor_set(x_346, 1, x_345);
lean_ctor_set(x_346, 2, x_32);
x_347 = lean_array_uset(x_18, x_31, x_346);
x_348 = lean_unsigned_to_nat(4u);
x_349 = lean_nat_mul(x_344, x_348);
x_350 = lean_unsigned_to_nat(3u);
x_351 = lean_nat_div(x_349, x_350);
lean_dec(x_349);
x_352 = lean_array_get_size(x_347);
x_353 = lean_nat_dec_le(x_351, x_352);
lean_dec(x_352);
lean_dec(x_351);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(x_347);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_344);
lean_ctor_set(x_355, 1, x_354);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_2, 0);
lean_inc(x_356);
lean_dec(x_2);
x_357 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5(x_1, x_356, x_355, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_357;
}
case 5:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_358 = lean_ctor_get(x_2, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_2, 1);
lean_inc(x_359);
lean_dec(x_2);
x_360 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_358, x_355, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_359);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_364 = x_360;
} else {
 lean_dec_ref(x_360);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_361, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_366 = x_361;
} else {
 lean_dec_ref(x_361);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_362, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_368 = x_362;
} else {
 lean_dec_ref(x_362);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(0, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
if (lean_is_scalar(x_366)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_366;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_365);
if (lean_is_scalar(x_364)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_364;
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_363);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; 
lean_dec(x_362);
x_372 = lean_ctor_get(x_360, 1);
lean_inc(x_372);
lean_dec(x_360);
x_373 = lean_ctor_get(x_361, 1);
lean_inc(x_373);
lean_dec(x_361);
x_2 = x_359;
x_3 = x_373;
x_12 = x_372;
goto _start;
}
}
case 6:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_375 = lean_ctor_get(x_2, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_2, 2);
lean_inc(x_376);
lean_dec(x_2);
x_377 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_375, x_355, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_376);
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_381 = x_377;
} else {
 lean_dec_ref(x_377);
 x_381 = lean_box(0);
}
x_382 = lean_ctor_get(x_378, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_383 = x_378;
} else {
 lean_dec_ref(x_378);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_379, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 x_385 = x_379;
} else {
 lean_dec_ref(x_379);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(0, 1, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_384);
if (lean_is_scalar(x_383)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_383;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_382);
if (lean_is_scalar(x_381)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_381;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_380);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_379);
x_389 = lean_ctor_get(x_377, 1);
lean_inc(x_389);
lean_dec(x_377);
x_390 = lean_ctor_get(x_378, 1);
lean_inc(x_390);
lean_dec(x_378);
x_2 = x_376;
x_3 = x_390;
x_12 = x_389;
goto _start;
}
}
case 7:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_392 = lean_ctor_get(x_2, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_2, 2);
lean_inc(x_393);
lean_dec(x_2);
x_394 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_392, x_355, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_393);
x_397 = lean_ctor_get(x_394, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_398 = x_394;
} else {
 lean_dec_ref(x_394);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_395, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_400 = x_395;
} else {
 lean_dec_ref(x_395);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_396, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_402 = x_396;
} else {
 lean_dec_ref(x_396);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(0, 1, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_401);
if (lean_is_scalar(x_400)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_400;
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_399);
if (lean_is_scalar(x_398)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_398;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_397);
return x_405;
}
else
{
lean_object* x_406; lean_object* x_407; 
lean_dec(x_396);
x_406 = lean_ctor_get(x_394, 1);
lean_inc(x_406);
lean_dec(x_394);
x_407 = lean_ctor_get(x_395, 1);
lean_inc(x_407);
lean_dec(x_395);
x_2 = x_393;
x_3 = x_407;
x_12 = x_406;
goto _start;
}
}
case 8:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_409 = lean_ctor_get(x_2, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_2, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_2, 3);
lean_inc(x_411);
lean_dec(x_2);
x_412 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_409, x_355, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_411);
lean_dec(x_410);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_416 = x_412;
} else {
 lean_dec_ref(x_412);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_413, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_418 = x_413;
} else {
 lean_dec_ref(x_413);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_414, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 x_420 = x_414;
} else {
 lean_dec_ref(x_414);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(0, 1, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_419);
if (lean_is_scalar(x_418)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_418;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_417);
if (lean_is_scalar(x_416)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_416;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_415);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_414);
x_424 = lean_ctor_get(x_412, 1);
lean_inc(x_424);
lean_dec(x_412);
x_425 = lean_ctor_get(x_413, 1);
lean_inc(x_425);
lean_dec(x_413);
x_426 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_410, x_425, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_424);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_411);
x_429 = lean_ctor_get(x_426, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_430 = x_426;
} else {
 lean_dec_ref(x_426);
 x_430 = lean_box(0);
}
x_431 = lean_ctor_get(x_427, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_432 = x_427;
} else {
 lean_dec_ref(x_427);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_428, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 x_434 = x_428;
} else {
 lean_dec_ref(x_428);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(0, 1, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_433);
if (lean_is_scalar(x_432)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_432;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_431);
if (lean_is_scalar(x_430)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_430;
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_429);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_428);
x_438 = lean_ctor_get(x_426, 1);
lean_inc(x_438);
lean_dec(x_426);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
lean_dec(x_427);
x_2 = x_411;
x_3 = x_439;
x_12 = x_438;
goto _start;
}
}
}
case 10:
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_2, 1);
lean_inc(x_441);
lean_dec(x_2);
x_2 = x_441;
x_3 = x_355;
goto _start;
}
case 11:
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_2, 2);
lean_inc(x_443);
lean_dec(x_2);
x_2 = x_443;
x_3 = x_355;
goto _start;
}
default: 
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_2);
x_445 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_355);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_12);
return x_447;
}
}
}
else
{
lean_object* x_448; 
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_344);
lean_ctor_set(x_448, 1, x_347);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_2, 0);
lean_inc(x_449);
lean_dec(x_2);
x_450 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5(x_1, x_449, x_448, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_450;
}
case 5:
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_451 = lean_ctor_get(x_2, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_2, 1);
lean_inc(x_452);
lean_dec(x_2);
x_453 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_451, x_448, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_452);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_457 = x_453;
} else {
 lean_dec_ref(x_453);
 x_457 = lean_box(0);
}
x_458 = lean_ctor_get(x_454, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_459 = x_454;
} else {
 lean_dec_ref(x_454);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_455, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_461 = x_455;
} else {
 lean_dec_ref(x_455);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(0, 1, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_460);
if (lean_is_scalar(x_459)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_459;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_458);
if (lean_is_scalar(x_457)) {
 x_464 = lean_alloc_ctor(0, 2, 0);
} else {
 x_464 = x_457;
}
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_456);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; 
lean_dec(x_455);
x_465 = lean_ctor_get(x_453, 1);
lean_inc(x_465);
lean_dec(x_453);
x_466 = lean_ctor_get(x_454, 1);
lean_inc(x_466);
lean_dec(x_454);
x_2 = x_452;
x_3 = x_466;
x_12 = x_465;
goto _start;
}
}
case 6:
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_468 = lean_ctor_get(x_2, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_2, 2);
lean_inc(x_469);
lean_dec(x_2);
x_470 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_468, x_448, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_469);
x_473 = lean_ctor_get(x_470, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_474 = x_470;
} else {
 lean_dec_ref(x_470);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_471, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_476 = x_471;
} else {
 lean_dec_ref(x_471);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_472, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 x_478 = x_472;
} else {
 lean_dec_ref(x_472);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(0, 1, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_477);
if (lean_is_scalar(x_476)) {
 x_480 = lean_alloc_ctor(0, 2, 0);
} else {
 x_480 = x_476;
}
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_475);
if (lean_is_scalar(x_474)) {
 x_481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_481 = x_474;
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_473);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; 
lean_dec(x_472);
x_482 = lean_ctor_get(x_470, 1);
lean_inc(x_482);
lean_dec(x_470);
x_483 = lean_ctor_get(x_471, 1);
lean_inc(x_483);
lean_dec(x_471);
x_2 = x_469;
x_3 = x_483;
x_12 = x_482;
goto _start;
}
}
case 7:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_485 = lean_ctor_get(x_2, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_2, 2);
lean_inc(x_486);
lean_dec(x_2);
x_487 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_485, x_448, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_486);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_491 = x_487;
} else {
 lean_dec_ref(x_487);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_488, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_493 = x_488;
} else {
 lean_dec_ref(x_488);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_489, 0);
lean_inc(x_494);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 x_495 = x_489;
} else {
 lean_dec_ref(x_489);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(0, 1, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_494);
if (lean_is_scalar(x_493)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_493;
}
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_492);
if (lean_is_scalar(x_491)) {
 x_498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_498 = x_491;
}
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_490);
return x_498;
}
else
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_489);
x_499 = lean_ctor_get(x_487, 1);
lean_inc(x_499);
lean_dec(x_487);
x_500 = lean_ctor_get(x_488, 1);
lean_inc(x_500);
lean_dec(x_488);
x_2 = x_486;
x_3 = x_500;
x_12 = x_499;
goto _start;
}
}
case 8:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_502 = lean_ctor_get(x_2, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_2, 2);
lean_inc(x_503);
x_504 = lean_ctor_get(x_2, 3);
lean_inc(x_504);
lean_dec(x_2);
x_505 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_502, x_448, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_504);
lean_dec(x_503);
x_508 = lean_ctor_get(x_505, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_509 = x_505;
} else {
 lean_dec_ref(x_505);
 x_509 = lean_box(0);
}
x_510 = lean_ctor_get(x_506, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_511 = x_506;
} else {
 lean_dec_ref(x_506);
 x_511 = lean_box(0);
}
x_512 = lean_ctor_get(x_507, 0);
lean_inc(x_512);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 x_513 = x_507;
} else {
 lean_dec_ref(x_507);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(0, 1, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_512);
if (lean_is_scalar(x_511)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_511;
}
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_510);
if (lean_is_scalar(x_509)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_509;
}
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_508);
return x_516;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_507);
x_517 = lean_ctor_get(x_505, 1);
lean_inc(x_517);
lean_dec(x_505);
x_518 = lean_ctor_get(x_506, 1);
lean_inc(x_518);
lean_dec(x_506);
x_519 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_503, x_518, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_517);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_504);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_523 = x_519;
} else {
 lean_dec_ref(x_519);
 x_523 = lean_box(0);
}
x_524 = lean_ctor_get(x_520, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_525 = x_520;
} else {
 lean_dec_ref(x_520);
 x_525 = lean_box(0);
}
x_526 = lean_ctor_get(x_521, 0);
lean_inc(x_526);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 x_527 = x_521;
} else {
 lean_dec_ref(x_521);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(0, 1, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_526);
if (lean_is_scalar(x_525)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_525;
}
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_524);
if (lean_is_scalar(x_523)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_523;
}
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_522);
return x_530;
}
else
{
lean_object* x_531; lean_object* x_532; 
lean_dec(x_521);
x_531 = lean_ctor_get(x_519, 1);
lean_inc(x_531);
lean_dec(x_519);
x_532 = lean_ctor_get(x_520, 1);
lean_inc(x_532);
lean_dec(x_520);
x_2 = x_504;
x_3 = x_532;
x_12 = x_531;
goto _start;
}
}
}
case 10:
{
lean_object* x_534; 
x_534 = lean_ctor_get(x_2, 1);
lean_inc(x_534);
lean_dec(x_2);
x_2 = x_534;
x_3 = x_448;
goto _start;
}
case 11:
{
lean_object* x_536; 
x_536 = lean_ctor_get(x_2, 2);
lean_inc(x_536);
lean_dec(x_2);
x_2 = x_536;
x_3 = x_448;
goto _start;
}
default: 
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_2);
x_538 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_448);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_12);
return x_540;
}
}
}
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
x_541 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1;
x_542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_3);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_12);
return x_543;
}
}
}
}
static lean_object* _init_l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasExprMVar(x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__3;
x_17 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
lean_dec(x_29);
x_30 = 1;
x_31 = lean_box(x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_10, 5);
lean_inc(x_13);
x_14 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_19 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__3;
lean_inc(x_11);
lean_inc(x_10);
x_20 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_17, x_18, x_19, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_10(x_2, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpa", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("using", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSimpa!_", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpa!", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Tactic.Simpa.evalSimpa", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__18;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__19;
x_3 = lean_unsigned_to_nat(105u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__20;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_152; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_293 = lean_unsigned_to_nat(5u);
x_294 = l_Lean_Syntax_getArg(x_7, x_293);
x_295 = lean_unsigned_to_nat(0u);
x_296 = l_Lean_Syntax_matchesNull(x_294, x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_298 = l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2(x_297, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_apply_10(x_5, x_299, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_300);
return x_301;
}
else
{
uint8_t x_302; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
x_302 = !lean_is_exclusive(x_298);
if (x_302 == 0)
{
return x_298;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_298, 0);
x_304 = lean_ctor_get(x_298, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_298);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
lean_object* x_306; 
x_306 = l_Lean_Syntax_getOptional_x3f(x_8);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = lean_box(0);
if (x_9 == 0)
{
x_21 = x_307;
goto block_151;
}
else
{
lean_dec(x_4);
x_152 = x_307;
goto block_292;
}
}
else
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_306);
if (x_308 == 0)
{
if (x_9 == 0)
{
x_21 = x_306;
goto block_151;
}
else
{
lean_dec(x_4);
x_152 = x_306;
goto block_292;
}
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_306, 0);
lean_inc(x_309);
lean_dec(x_306);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_309);
if (x_9 == 0)
{
x_21 = x_310;
goto block_151;
}
else
{
lean_dec(x_4);
x_152 = x_310;
goto block_292;
}
}
}
}
block_151:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_18, 5);
lean_inc(x_22);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_19, x_20);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1;
lean_inc(x_24);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_29);
lean_ctor_set(x_25, 0, x_24);
x_30 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3;
x_31 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
lean_inc(x_24);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
if (lean_obj_tag(x_21) == 0)
{
x_33 = x_31;
goto block_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_21, 0);
lean_inc(x_87);
lean_dec(x_21);
x_88 = lean_array_push(x_31, x_87);
x_33 = x_88;
goto block_86;
}
block_86:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Array_append___rarg(x_31, x_33);
lean_dec(x_33);
lean_inc(x_24);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_34);
if (lean_obj_tag(x_6) == 0)
{
x_36 = x_31;
goto block_79;
}
else
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_6, 0);
x_81 = 1;
x_82 = l_Lean_SourceInfo_fromRef(x_80, x_81);
x_83 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14;
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Array_mkArray1___rarg(x_84);
x_36 = x_85;
goto block_79;
}
block_79:
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Array_append___rarg(x_31, x_36);
lean_dec(x_36);
lean_inc(x_24);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_37);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_24);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_39);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_40);
lean_inc(x_24);
x_41 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_35, x_38, x_40, x_40);
lean_inc(x_32);
x_42 = l_Lean_Syntax_node4(x_24, x_4, x_25, x_32, x_32, x_41);
x_43 = lean_apply_10(x_5, x_42, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_27);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_24);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Array_mkArray2___rarg(x_46, x_44);
x_48 = l_Array_append___rarg(x_31, x_47);
lean_dec(x_47);
lean_inc(x_24);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_49, 1, x_30);
lean_ctor_set(x_49, 2, x_48);
lean_inc(x_24);
x_50 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_35, x_38, x_40, x_49);
lean_inc(x_32);
x_51 = l_Lean_Syntax_node4(x_24, x_4, x_25, x_32, x_32, x_50);
x_52 = lean_apply_10(x_5, x_51, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_27);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_24);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_24);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_append___rarg(x_31, x_53);
lean_inc(x_24);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_24);
lean_ctor_set(x_57, 1, x_30);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_24);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_24);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11;
lean_inc(x_24);
x_61 = l_Lean_Syntax_node3(x_24, x_60, x_55, x_57, x_59);
x_62 = l_Array_mkArray1___rarg(x_61);
x_63 = l_Array_append___rarg(x_31, x_62);
lean_dec(x_62);
lean_inc(x_24);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_30);
lean_ctor_set(x_64, 2, x_63);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_24);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_24);
lean_ctor_set(x_66, 1, x_30);
lean_ctor_set(x_66, 2, x_65);
lean_inc(x_24);
x_67 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_35, x_38, x_64, x_66);
lean_inc(x_32);
x_68 = l_Lean_Syntax_node4(x_24, x_4, x_25, x_32, x_32, x_67);
x_69 = lean_apply_10(x_5, x_68, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_27);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_24);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_24);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Array_mkArray2___rarg(x_72, x_70);
x_74 = l_Array_append___rarg(x_31, x_73);
lean_dec(x_73);
lean_inc(x_24);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_24);
lean_ctor_set(x_75, 1, x_30);
lean_ctor_set(x_75, 2, x_74);
lean_inc(x_24);
x_76 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_35, x_38, x_64, x_75);
lean_inc(x_32);
x_77 = l_Lean_Syntax_node4(x_24, x_4, x_25, x_32, x_32, x_76);
x_78 = lean_apply_10(x_5, x_77, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_27);
return x_78;
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_25, 1);
lean_inc(x_89);
lean_dec(x_25);
x_90 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1;
lean_inc(x_24);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_24);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3;
x_93 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
lean_inc(x_24);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_24);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_93);
if (lean_obj_tag(x_21) == 0)
{
x_95 = x_93;
goto block_148;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_21, 0);
lean_inc(x_149);
lean_dec(x_21);
x_150 = lean_array_push(x_93, x_149);
x_95 = x_150;
goto block_148;
}
block_148:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = l_Array_append___rarg(x_93, x_95);
lean_dec(x_95);
lean_inc(x_24);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_24);
lean_ctor_set(x_97, 1, x_92);
lean_ctor_set(x_97, 2, x_96);
if (lean_obj_tag(x_6) == 0)
{
x_98 = x_93;
goto block_141;
}
else
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_6, 0);
x_143 = 1;
x_144 = l_Lean_SourceInfo_fromRef(x_142, x_143);
x_145 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14;
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Array_mkArray1___rarg(x_146);
x_98 = x_147;
goto block_141;
}
block_141:
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Array_append___rarg(x_93, x_98);
lean_dec(x_98);
lean_inc(x_24);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_24);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_99);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_24);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_24);
lean_ctor_set(x_102, 1, x_92);
lean_ctor_set(x_102, 2, x_101);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_inc(x_102);
lean_inc(x_24);
x_103 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_97, x_100, x_102, x_102);
lean_inc(x_94);
x_104 = l_Lean_Syntax_node4(x_24, x_4, x_91, x_94, x_94, x_103);
x_105 = lean_apply_10(x_5, x_104, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_89);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_24);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_24);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Array_mkArray2___rarg(x_108, x_106);
x_110 = l_Array_append___rarg(x_93, x_109);
lean_dec(x_109);
lean_inc(x_24);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_24);
lean_ctor_set(x_111, 1, x_92);
lean_ctor_set(x_111, 2, x_110);
lean_inc(x_24);
x_112 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_97, x_100, x_102, x_111);
lean_inc(x_94);
x_113 = l_Lean_Syntax_node4(x_24, x_4, x_91, x_94, x_94, x_112);
x_114 = lean_apply_10(x_5, x_113, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_89);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_115 = lean_ctor_get(x_11, 0);
x_116 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_24);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_24);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_append___rarg(x_93, x_115);
lean_inc(x_24);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_24);
lean_ctor_set(x_119, 1, x_92);
lean_ctor_set(x_119, 2, x_118);
x_120 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_24);
x_121 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_121, 0, x_24);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11;
lean_inc(x_24);
x_123 = l_Lean_Syntax_node3(x_24, x_122, x_117, x_119, x_121);
x_124 = l_Array_mkArray1___rarg(x_123);
x_125 = l_Array_append___rarg(x_93, x_124);
lean_dec(x_124);
lean_inc(x_24);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_24);
lean_ctor_set(x_126, 1, x_92);
lean_ctor_set(x_126, 2, x_125);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_24);
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_24);
lean_ctor_set(x_128, 1, x_92);
lean_ctor_set(x_128, 2, x_127);
lean_inc(x_24);
x_129 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_97, x_100, x_126, x_128);
lean_inc(x_94);
x_130 = l_Lean_Syntax_node4(x_24, x_4, x_91, x_94, x_94, x_129);
x_131 = lean_apply_10(x_5, x_130, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_89);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = lean_ctor_get(x_1, 0);
lean_inc(x_132);
lean_dec(x_1);
x_133 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_24);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_24);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Array_mkArray2___rarg(x_134, x_132);
x_136 = l_Array_append___rarg(x_93, x_135);
lean_dec(x_135);
lean_inc(x_24);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_24);
lean_ctor_set(x_137, 1, x_92);
lean_ctor_set(x_137, 2, x_136);
lean_inc(x_24);
x_138 = l_Lean_Syntax_node5(x_24, x_2, x_3, x_97, x_100, x_126, x_137);
lean_inc(x_94);
x_139 = l_Lean_Syntax_node4(x_24, x_4, x_91, x_94, x_94, x_138);
x_140 = lean_apply_10(x_5, x_139, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_89);
return x_140;
}
}
}
}
}
}
block_292:
{
lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_18, 5);
lean_inc(x_153);
x_154 = 0;
x_155 = l_Lean_SourceInfo_fromRef(x_153, x_154);
lean_dec(x_153);
x_156 = lean_st_ref_get(x_19, x_20);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_156, 1);
x_159 = lean_ctor_get(x_156, 0);
lean_dec(x_159);
x_160 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__17;
lean_inc(x_155);
lean_ctor_set_tag(x_156, 2);
lean_ctor_set(x_156, 1, x_160);
lean_ctor_set(x_156, 0, x_155);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_221; 
x_221 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
x_161 = x_221;
goto block_220;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_152, 0);
lean_inc(x_222);
lean_dec(x_152);
x_223 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
x_224 = lean_array_push(x_223, x_222);
x_161 = x_224;
goto block_220;
}
block_220:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
x_163 = l_Array_append___rarg(x_162, x_161);
lean_dec(x_161);
x_164 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3;
lean_inc(x_155);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_163);
if (lean_obj_tag(x_6) == 0)
{
x_166 = x_162;
goto block_213;
}
else
{
lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_6, 0);
x_215 = 1;
x_216 = l_Lean_SourceInfo_fromRef(x_214, x_215);
x_217 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14;
x_218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Array_mkArray1___rarg(x_218);
x_166 = x_219;
goto block_213;
}
block_213:
{
lean_object* x_167; lean_object* x_168; 
x_167 = l_Array_append___rarg(x_162, x_166);
lean_dec(x_166);
lean_inc(x_155);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_155);
lean_ctor_set(x_168, 1, x_164);
lean_ctor_set(x_168, 2, x_167);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_155);
x_170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_170, 0, x_155);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_169);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_inc(x_170);
lean_inc(x_155);
x_171 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_165, x_168, x_170, x_170);
x_172 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_173 = l_Lean_Syntax_node2(x_155, x_172, x_156, x_171);
x_174 = lean_apply_10(x_5, x_173, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_158);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_175 = lean_ctor_get(x_1, 0);
lean_inc(x_175);
lean_dec(x_1);
x_176 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_155);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_155);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Array_mkArray2___rarg(x_177, x_175);
x_179 = l_Array_append___rarg(x_162, x_178);
lean_dec(x_178);
lean_inc(x_155);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_155);
lean_ctor_set(x_180, 1, x_164);
lean_ctor_set(x_180, 2, x_179);
lean_inc(x_155);
x_181 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_165, x_168, x_170, x_180);
x_182 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_183 = l_Lean_Syntax_node2(x_155, x_182, x_156, x_181);
x_184 = lean_apply_10(x_5, x_183, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_158);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_185 = lean_ctor_get(x_11, 0);
x_186 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_155);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_155);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Array_append___rarg(x_162, x_185);
lean_inc(x_155);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_155);
lean_ctor_set(x_189, 1, x_164);
lean_ctor_set(x_189, 2, x_188);
x_190 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_155);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_155);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11;
lean_inc(x_155);
x_193 = l_Lean_Syntax_node3(x_155, x_192, x_187, x_189, x_191);
x_194 = l_Array_mkArray1___rarg(x_193);
x_195 = l_Array_append___rarg(x_162, x_194);
lean_dec(x_194);
lean_inc(x_155);
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_155);
lean_ctor_set(x_196, 1, x_164);
lean_ctor_set(x_196, 2, x_195);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_197 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_155);
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_155);
lean_ctor_set(x_198, 1, x_164);
lean_ctor_set(x_198, 2, x_197);
lean_inc(x_155);
x_199 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_165, x_168, x_196, x_198);
x_200 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_201 = l_Lean_Syntax_node2(x_155, x_200, x_156, x_199);
x_202 = lean_apply_10(x_5, x_201, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_158);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_203 = lean_ctor_get(x_1, 0);
lean_inc(x_203);
lean_dec(x_1);
x_204 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_155);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_155);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Array_mkArray2___rarg(x_205, x_203);
x_207 = l_Array_append___rarg(x_162, x_206);
lean_dec(x_206);
lean_inc(x_155);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_155);
lean_ctor_set(x_208, 1, x_164);
lean_ctor_set(x_208, 2, x_207);
lean_inc(x_155);
x_209 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_165, x_168, x_196, x_208);
x_210 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_211 = l_Lean_Syntax_node2(x_155, x_210, x_156, x_209);
x_212 = lean_apply_10(x_5, x_211, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_158);
return x_212;
}
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_156, 1);
lean_inc(x_225);
lean_dec(x_156);
x_226 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__17;
lean_inc(x_155);
x_227 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_227, 0, x_155);
lean_ctor_set(x_227, 1, x_226);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_288; 
x_288 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
x_228 = x_288;
goto block_287;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_152, 0);
lean_inc(x_289);
lean_dec(x_152);
x_290 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
x_291 = lean_array_push(x_290, x_289);
x_228 = x_291;
goto block_287;
}
block_287:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
x_230 = l_Array_append___rarg(x_229, x_228);
lean_dec(x_228);
x_231 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3;
lean_inc(x_155);
x_232 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_232, 0, x_155);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_230);
if (lean_obj_tag(x_6) == 0)
{
x_233 = x_229;
goto block_280;
}
else
{
lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_281 = lean_ctor_get(x_6, 0);
x_282 = 1;
x_283 = l_Lean_SourceInfo_fromRef(x_281, x_282);
x_284 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14;
x_285 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = l_Array_mkArray1___rarg(x_285);
x_233 = x_286;
goto block_280;
}
block_280:
{
lean_object* x_234; lean_object* x_235; 
x_234 = l_Array_append___rarg(x_229, x_233);
lean_dec(x_233);
lean_inc(x_155);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_155);
lean_ctor_set(x_235, 1, x_231);
lean_ctor_set(x_235, 2, x_234);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_155);
x_237 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_237, 0, x_155);
lean_ctor_set(x_237, 1, x_231);
lean_ctor_set(x_237, 2, x_236);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_inc(x_237);
lean_inc(x_155);
x_238 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_232, x_235, x_237, x_237);
x_239 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_240 = l_Lean_Syntax_node2(x_155, x_239, x_227, x_238);
x_241 = lean_apply_10(x_5, x_240, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_225);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_242 = lean_ctor_get(x_1, 0);
lean_inc(x_242);
lean_dec(x_1);
x_243 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_155);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_155);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Array_mkArray2___rarg(x_244, x_242);
x_246 = l_Array_append___rarg(x_229, x_245);
lean_dec(x_245);
lean_inc(x_155);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_155);
lean_ctor_set(x_247, 1, x_231);
lean_ctor_set(x_247, 2, x_246);
lean_inc(x_155);
x_248 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_232, x_235, x_237, x_247);
x_249 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_250 = l_Lean_Syntax_node2(x_155, x_249, x_227, x_248);
x_251 = lean_apply_10(x_5, x_250, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_225);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_252 = lean_ctor_get(x_11, 0);
x_253 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_155);
x_254 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_254, 0, x_155);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Array_append___rarg(x_229, x_252);
lean_inc(x_155);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_155);
lean_ctor_set(x_256, 1, x_231);
lean_ctor_set(x_256, 2, x_255);
x_257 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_155);
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_155);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11;
lean_inc(x_155);
x_260 = l_Lean_Syntax_node3(x_155, x_259, x_254, x_256, x_258);
x_261 = l_Array_mkArray1___rarg(x_260);
x_262 = l_Array_append___rarg(x_229, x_261);
lean_dec(x_261);
lean_inc(x_155);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_155);
lean_ctor_set(x_263, 1, x_231);
lean_ctor_set(x_263, 2, x_262);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_155);
x_265 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_265, 0, x_155);
lean_ctor_set(x_265, 1, x_231);
lean_ctor_set(x_265, 2, x_264);
lean_inc(x_155);
x_266 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_232, x_235, x_263, x_265);
x_267 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_268 = l_Lean_Syntax_node2(x_155, x_267, x_227, x_266);
x_269 = lean_apply_10(x_5, x_268, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_225);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_270 = lean_ctor_get(x_1, 0);
lean_inc(x_270);
lean_dec(x_1);
x_271 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6;
lean_inc(x_155);
x_272 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_272, 0, x_155);
lean_ctor_set(x_272, 1, x_271);
x_273 = l_Array_mkArray2___rarg(x_272, x_270);
x_274 = l_Array_append___rarg(x_229, x_273);
lean_dec(x_273);
lean_inc(x_155);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_155);
lean_ctor_set(x_275, 1, x_231);
lean_ctor_set(x_275, 2, x_274);
lean_inc(x_155);
x_276 = l_Lean_Syntax_node5(x_155, x_2, x_3, x_232, x_235, x_263, x_275);
x_277 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16;
x_278 = l_Lean_Syntax_node2(x_155, x_277, x_227, x_276);
x_279 = lean_apply_10(x_5, x_278, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_225);
return x_279;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_isNone(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_unsigned_to_nat(3u);
lean_inc(x_21);
x_24 = l_Lean_Syntax_matchesNull(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2(x_25, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_apply_10(x_6, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = l_Lean_Syntax_getArg(x_21, x_34);
lean_dec(x_21);
x_36 = l_Lean_Syntax_getArgs(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4(x_2, x_3, x_4, x_5, x_6, x_10, x_1, x_7, x_8, x_38, x_37, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
x_40 = lean_box(0);
x_41 = lean_box(0);
x_42 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4(x_2, x_3, x_4, x_5, x_6, x_10, x_1, x_7, x_8, x_41, x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_42;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tactic_simp_trace;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_84; uint8_t x_85; 
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_inc(x_9);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__2___boxed), 11, 1);
lean_closure_set(x_20, 0, x_9);
x_84 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__3;
x_85 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_19, x_84);
lean_dec(x_19);
if (x_85 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__2(x_9, x_86, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_87;
}
else
{
lean_object* x_88; 
x_88 = lean_box(0);
x_21 = x_88;
goto block_83;
}
}
else
{
lean_object* x_89; 
x_89 = lean_box(0);
x_21 = x_89;
goto block_83;
}
block_83:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
x_22 = l_Lean_Syntax_unsetTrailing(x_1);
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_24 = x_76;
goto block_75;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_7);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_7, 0);
x_79 = l_Lean_Syntax_unsetTrailing(x_78);
lean_ctor_set(x_7, 0, x_79);
x_24 = x_7;
goto block_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_7, 0);
lean_inc(x_80);
lean_dec(x_7);
x_81 = l_Lean_Syntax_unsetTrailing(x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_24 = x_82;
goto block_75;
}
}
block_75:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_inc(x_16);
lean_inc(x_14);
x_25 = l_Lean_Elab_Tactic_mkSimpOnly(x_22, x_23, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_20);
lean_inc(x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___boxed), 12, 2);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_20);
x_29 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
lean_inc(x_26);
x_30 = l_Lean_Syntax_isOfKind(x_26, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
x_31 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_32 = l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2(x_31, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3(x_2, x_20, x_33, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_34);
lean_dec(x_2);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(1u);
x_41 = l_Lean_Syntax_getArg(x_26, x_40);
lean_inc(x_41);
x_42 = l_Lean_Syntax_isOfKind(x_41, x_3);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
x_43 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_44 = l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2(x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_27);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3(x_2, x_20, x_45, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_46);
lean_dec(x_2);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_unsigned_to_nat(2u);
x_53 = l_Lean_Syntax_getArg(x_26, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = l_Lean_Syntax_getArg(x_26, x_54);
x_56 = l_Lean_Syntax_isNone(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
lean_inc(x_55);
x_57 = l_Lean_Syntax_matchesNull(x_55, x_40);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_41);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_5);
lean_dec(x_4);
x_58 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_59 = l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2(x_58, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_27);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3(x_2, x_20, x_60, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_61);
lean_dec(x_2);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_20);
lean_dec(x_2);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Lean_Syntax_getArg(x_55, x_67);
lean_dec(x_55);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_box(0);
x_71 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__5(x_26, x_24, x_4, x_41, x_5, x_28, x_53, x_6, x_70, x_69, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_27);
lean_dec(x_69);
lean_dec(x_53);
lean_dec(x_26);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = lean_box(0);
x_74 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__5(x_26, x_24, x_4, x_41, x_5, x_28, x_53, x_6, x_73, x_72, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_27);
lean_dec(x_53);
lean_dec(x_26);
return x_74;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_10(x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_Meta_getMVars(x_1, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_filterOldMVars(x_15, x_2, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___closed__1;
x_23 = 0;
x_24 = l_Lean_Elab_Tactic_closeMainGoal(x_22, x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type mismatch, term", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nafter simplification", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_MVarId_getType(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_mk_syntax_ident(x_2);
lean_inc(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Elab_Term_elabTerm(x_18, x_19, x_20, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_24, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_22);
x_28 = lean_infer_type(x_22, x_10, x_11, x_12, x_13, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_10, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_10, 5);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
x_39 = lean_ctor_get_uint8(x_10, sizeof(void*)*6 + 1);
lean_ctor_set_uint8(x_29, 7, x_20);
x_40 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*6 + 1, x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_30);
lean_inc(x_16);
x_41 = l_Lean_Meta_isExprDefEq(x_16, x_30, x_40, x_11, x_12, x_13, x_31);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_9);
lean_dec(x_8);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_indentExpr(x_3);
x_46 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_inc(x_5);
x_51 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_50, x_16, x_30, x_22, x_5, x_5, x_10, x_11, x_12, x_13, x_44);
lean_dec(x_5);
lean_dec(x_50);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_5);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_dec(x_41);
x_57 = lean_box(0);
x_58 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8(x_3, x_4, x_22, x_57, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_41);
if (x_59 == 0)
{
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_41, 0);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_41);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
x_64 = lean_ctor_get_uint8(x_10, sizeof(void*)*6 + 1);
x_65 = lean_ctor_get_uint8(x_29, 0);
x_66 = lean_ctor_get_uint8(x_29, 1);
x_67 = lean_ctor_get_uint8(x_29, 2);
x_68 = lean_ctor_get_uint8(x_29, 3);
x_69 = lean_ctor_get_uint8(x_29, 4);
x_70 = lean_ctor_get_uint8(x_29, 5);
x_71 = lean_ctor_get_uint8(x_29, 6);
x_72 = lean_ctor_get_uint8(x_29, 8);
x_73 = lean_ctor_get_uint8(x_29, 9);
x_74 = lean_ctor_get_uint8(x_29, 10);
x_75 = lean_ctor_get_uint8(x_29, 11);
x_76 = lean_ctor_get_uint8(x_29, 12);
lean_dec(x_29);
x_77 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_77, 0, x_65);
lean_ctor_set_uint8(x_77, 1, x_66);
lean_ctor_set_uint8(x_77, 2, x_67);
lean_ctor_set_uint8(x_77, 3, x_68);
lean_ctor_set_uint8(x_77, 4, x_69);
lean_ctor_set_uint8(x_77, 5, x_70);
lean_ctor_set_uint8(x_77, 6, x_71);
lean_ctor_set_uint8(x_77, 7, x_20);
lean_ctor_set_uint8(x_77, 8, x_72);
lean_ctor_set_uint8(x_77, 9, x_73);
lean_ctor_set_uint8(x_77, 10, x_74);
lean_ctor_set_uint8(x_77, 11, x_75);
lean_ctor_set_uint8(x_77, 12, x_76);
x_78 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_32);
lean_ctor_set(x_78, 2, x_33);
lean_ctor_set(x_78, 3, x_34);
lean_ctor_set(x_78, 4, x_35);
lean_ctor_set(x_78, 5, x_36);
lean_ctor_set_uint8(x_78, sizeof(void*)*6, x_63);
lean_ctor_set_uint8(x_78, sizeof(void*)*6 + 1, x_64);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_30);
lean_inc(x_16);
x_79 = l_Lean_Meta_isExprDefEq(x_16, x_30, x_78, x_11, x_12, x_13, x_31);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_9);
lean_dec(x_8);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l_Lean_indentExpr(x_3);
x_84 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__2;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__4;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_inc(x_5);
x_89 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_88, x_16, x_30, x_22, x_5, x_5, x_10, x_11, x_12, x_13, x_82);
lean_dec(x_5);
lean_dec(x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_5);
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
lean_dec(x_79);
x_95 = lean_box(0);
x_96 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8(x_3, x_4, x_22, x_95, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_97 = lean_ctor_get(x_79, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_99 = x_79;
} else {
 lean_dec_ref(x_79);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_28);
if (x_101 == 0)
{
return x_28;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_28, 0);
x_103 = lean_ctor_get(x_28, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_28);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_26);
if (x_105 == 0)
{
return x_26;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_26, 0);
x_107 = lean_ctor_get(x_26, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_26);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_21);
if (x_109 == 0)
{
return x_21;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_21, 0);
x_111 = lean_ctor_get(x_21, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_21);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_15);
if (x_113 == 0)
{
return x_15;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_15, 0);
x_115 = lean_ctor_get(x_15, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_15);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try 'simp at ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instead of 'simpa using ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_1);
x_21 = l_Lean_MVarId_getType(x_1, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_1);
x_24 = l_Lean_MVarId_getTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_16);
x_27 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_22, x_25, x_16, x_17, x_18, x_19, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Expr_mvarId_x21(x_29);
x_32 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__2;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_MVarId_note(x_31, x_32, x_2, x_3, x_16, x_17, x_18, x_19, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_4);
lean_inc(x_37);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_4);
x_39 = lean_array_mk(x_34);
x_40 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_41 = l_Lean_Meta_simpGoal(x_38, x_5, x_6, x_7, x_40, x_39, x_8, x_16, x_17, x_18, x_19, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_37);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_18, 2);
lean_inc(x_48);
x_49 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
x_50 = l_Lean_Linter_getLinterValue(x_49, x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_42);
lean_free_object(x_27);
lean_dec(x_2);
x_51 = lean_box(0);
x_52 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_46, x_51, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
return x_52;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
lean_dec(x_2);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_inc(x_53);
x_55 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_54, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_free_object(x_42);
lean_free_object(x_27);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_46, x_56, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
x_58 = lean_ctor_get(x_18, 5);
lean_inc(x_58);
x_59 = l_Lean_Expr_fvar___override(x_53);
x_60 = l_Lean_MessageData_ofExpr(x_59);
x_61 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4;
lean_inc(x_60);
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_60);
lean_ctor_set(x_42, 0, x_61);
x_62 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_62);
lean_ctor_set(x_27, 0, x_42);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_27);
lean_ctor_set(x_63, 1, x_60);
x_64 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_18);
x_66 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(x_49, x_58, x_65, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
lean_dec(x_58);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_46, x_67, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_68);
lean_dec(x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_free_object(x_42);
lean_free_object(x_27);
lean_dec(x_2);
x_70 = lean_box(0);
x_71 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_46, x_70, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_dec(x_42);
x_73 = lean_ctor_get(x_18, 2);
lean_inc(x_73);
x_74 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
x_75 = l_Lean_Linter_getLinterValue(x_74, x_73);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_free_object(x_27);
lean_dec(x_2);
x_76 = lean_box(0);
x_77 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_72, x_76, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
return x_77;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
lean_dec(x_2);
x_79 = lean_ctor_get(x_16, 1);
lean_inc(x_79);
lean_inc(x_78);
x_80 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_79, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_78);
lean_free_object(x_27);
x_81 = lean_box(0);
x_82 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_72, x_81, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_80);
x_83 = lean_ctor_get(x_18, 5);
lean_inc(x_83);
x_84 = l_Lean_Expr_fvar___override(x_78);
x_85 = l_Lean_MessageData_ofExpr(x_84);
x_86 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4;
lean_inc(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_88);
lean_ctor_set(x_27, 0, x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_27);
lean_ctor_set(x_89, 1, x_85);
x_90 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_18);
x_92 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(x_74, x_83, x_91, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
lean_dec(x_83);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_72, x_93, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_94);
lean_dec(x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_free_object(x_27);
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_72, x_96, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_44);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
lean_free_object(x_27);
x_98 = lean_ctor_get(x_43, 0);
lean_inc(x_98);
lean_dec(x_43);
x_99 = lean_ctor_get(x_41, 1);
lean_inc(x_99);
lean_dec(x_41);
x_100 = lean_ctor_get(x_42, 1);
lean_inc(x_100);
lean_dec(x_42);
x_101 = lean_ctor_get(x_98, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_148 = lean_array_get_size(x_101);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_lt(x_149, x_148);
lean_dec(x_148);
if (x_150 == 0)
{
lean_dec(x_101);
x_103 = x_37;
goto block_147;
}
else
{
lean_object* x_151; 
lean_dec(x_37);
x_151 = lean_array_fget(x_101, x_149);
lean_dec(x_101);
x_103 = x_151;
goto block_147;
}
block_147:
{
lean_object* x_104; uint8_t x_105; 
x_104 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_32, x_18, x_19, x_99);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_106);
x_108 = l_Lean_MVarId_rename(x_102, x_103, x_106, x_16, x_17, x_18, x_19, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_109);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 1, x_4);
lean_ctor_set(x_104, 0, x_109);
x_111 = l_Lean_Elab_Tactic_setGoals(x_104, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
lean_inc(x_109);
x_113 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___boxed), 14, 5);
lean_closure_set(x_113, 0, x_109);
lean_closure_set(x_113, 1, x_106);
lean_closure_set(x_113, 2, x_2);
lean_closure_set(x_113, 3, x_10);
lean_closure_set(x_113, 4, x_3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_114 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_109, x_113, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_100, x_115, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_116);
lean_dec(x_115);
return x_117;
}
else
{
uint8_t x_118; 
lean_dec(x_100);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_114);
if (x_118 == 0)
{
return x_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 0);
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_114);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_free_object(x_104);
lean_dec(x_106);
lean_dec(x_100);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_108);
if (x_122 == 0)
{
return x_108;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_108, 0);
x_124 = lean_ctor_get(x_108, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_108);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_104, 0);
x_127 = lean_ctor_get(x_104, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_104);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_126);
x_128 = l_Lean_MVarId_rename(x_102, x_103, x_126, x_16, x_17, x_18, x_19, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_129);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_4);
x_132 = l_Lean_Elab_Tactic_setGoals(x_131, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_130);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
lean_inc(x_129);
x_134 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___boxed), 14, 5);
lean_closure_set(x_134, 0, x_129);
lean_closure_set(x_134, 1, x_126);
lean_closure_set(x_134, 2, x_2);
lean_closure_set(x_134, 3, x_10);
lean_closure_set(x_134, 4, x_3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_135 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_129, x_134, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_100, x_136, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_137);
lean_dec(x_136);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_100);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_141 = x_135;
} else {
 lean_dec_ref(x_135);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_126);
lean_dec(x_100);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_128, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_128, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_145 = x_128;
} else {
 lean_dec_ref(x_128);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_37);
lean_free_object(x_27);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_41);
if (x_152 == 0)
{
return x_41;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_41, 0);
x_154 = lean_ctor_get(x_41, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_41);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_34, 0);
x_157 = lean_ctor_get(x_34, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_34);
lean_inc(x_4);
lean_inc(x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_4);
x_159 = lean_array_mk(x_158);
x_160 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_161 = l_Lean_Meta_simpGoal(x_157, x_5, x_6, x_7, x_160, x_159, x_8, x_16, x_17, x_18, x_19, x_35);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_dec(x_156);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_166 = x_162;
} else {
 lean_dec_ref(x_162);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_18, 2);
lean_inc(x_167);
x_168 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
x_169 = l_Lean_Linter_getLinterValue(x_168, x_167);
lean_dec(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_166);
lean_free_object(x_27);
lean_dec(x_2);
x_170 = lean_box(0);
x_171 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_165, x_170, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_164);
return x_171;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_2, 0);
lean_inc(x_172);
lean_dec(x_2);
x_173 = lean_ctor_get(x_16, 1);
lean_inc(x_173);
lean_inc(x_172);
x_174 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_173, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_172);
lean_dec(x_166);
lean_free_object(x_27);
x_175 = lean_box(0);
x_176 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_165, x_175, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_164);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_174);
x_177 = lean_ctor_get(x_18, 5);
lean_inc(x_177);
x_178 = l_Lean_Expr_fvar___override(x_172);
x_179 = l_Lean_MessageData_ofExpr(x_178);
x_180 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4;
lean_inc(x_179);
if (lean_is_scalar(x_166)) {
 x_181 = lean_alloc_ctor(7, 2, 0);
} else {
 x_181 = x_166;
 lean_ctor_set_tag(x_181, 7);
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_182);
lean_ctor_set(x_27, 0, x_181);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_27);
lean_ctor_set(x_183, 1, x_179);
x_184 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8;
x_185 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
lean_inc(x_18);
x_186 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(x_168, x_177, x_185, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_164);
lean_dec(x_177);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_165, x_187, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_188);
lean_dec(x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_166);
lean_free_object(x_27);
lean_dec(x_2);
x_190 = lean_box(0);
x_191 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_165, x_190, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_164);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_free_object(x_27);
x_192 = lean_ctor_get(x_163, 0);
lean_inc(x_192);
lean_dec(x_163);
x_193 = lean_ctor_get(x_161, 1);
lean_inc(x_193);
lean_dec(x_161);
x_194 = lean_ctor_get(x_162, 1);
lean_inc(x_194);
lean_dec(x_162);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_dec(x_192);
x_222 = lean_array_get_size(x_195);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_nat_dec_lt(x_223, x_222);
lean_dec(x_222);
if (x_224 == 0)
{
lean_dec(x_195);
x_197 = x_156;
goto block_221;
}
else
{
lean_object* x_225; 
lean_dec(x_156);
x_225 = lean_array_fget(x_195, x_223);
lean_dec(x_195);
x_197 = x_225;
goto block_221;
}
block_221:
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_32, x_18, x_19, x_193);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_199);
x_202 = l_Lean_MVarId_rename(x_196, x_197, x_199, x_16, x_17, x_18, x_19, x_200);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_203);
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_201;
 lean_ctor_set_tag(x_205, 1);
}
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_4);
x_206 = l_Lean_Elab_Tactic_setGoals(x_205, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_204);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
lean_inc(x_203);
x_208 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___boxed), 14, 5);
lean_closure_set(x_208, 0, x_203);
lean_closure_set(x_208, 1, x_199);
lean_closure_set(x_208, 2, x_2);
lean_closure_set(x_208, 3, x_10);
lean_closure_set(x_208, 4, x_3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_209 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_203, x_208, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_207);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_29, x_9, x_194, x_210, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_211);
lean_dec(x_210);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_194);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
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
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_194);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_202, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_202, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_219 = x_202;
} else {
 lean_dec_ref(x_202);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_156);
lean_free_object(x_27);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = lean_ctor_get(x_161, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_161, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_228 = x_161;
} else {
 lean_dec_ref(x_161);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_free_object(x_27);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_33);
if (x_230 == 0)
{
return x_33;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_33, 0);
x_232 = lean_ctor_get(x_33, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_33);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_27, 0);
x_235 = lean_ctor_get(x_27, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_27);
x_236 = l_Lean_Expr_mvarId_x21(x_234);
x_237 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__2;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_2);
x_238 = l_Lean_MVarId_note(x_236, x_237, x_2, x_3, x_16, x_17, x_18, x_19, x_235);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_243 = x_239;
} else {
 lean_dec_ref(x_239);
 x_243 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_241);
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
 lean_ctor_set_tag(x_244, 1);
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_4);
x_245 = lean_array_mk(x_244);
x_246 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_247 = l_Lean_Meta_simpGoal(x_242, x_5, x_6, x_7, x_246, x_245, x_8, x_16, x_17, x_18, x_19, x_240);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_241);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_18, 2);
lean_inc(x_253);
x_254 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
x_255 = l_Lean_Linter_getLinterValue(x_254, x_253);
lean_dec(x_253);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_252);
lean_dec(x_2);
x_256 = lean_box(0);
x_257 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_234, x_9, x_251, x_256, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_250);
return x_257;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_2, 0);
lean_inc(x_258);
lean_dec(x_2);
x_259 = lean_ctor_get(x_16, 1);
lean_inc(x_259);
lean_inc(x_258);
x_260 = l_Lean_LocalContext_getRoundtrippingUserName_x3f(x_259, x_258);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_258);
lean_dec(x_252);
x_261 = lean_box(0);
x_262 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_234, x_9, x_251, x_261, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_250);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_260);
x_263 = lean_ctor_get(x_18, 5);
lean_inc(x_263);
x_264 = l_Lean_Expr_fvar___override(x_258);
x_265 = l_Lean_MessageData_ofExpr(x_264);
x_266 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4;
lean_inc(x_265);
if (lean_is_scalar(x_252)) {
 x_267 = lean_alloc_ctor(7, 2, 0);
} else {
 x_267 = x_252;
 lean_ctor_set_tag(x_267, 7);
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6;
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_265);
x_271 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8;
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
lean_inc(x_18);
x_273 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(x_254, x_263, x_272, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_250);
lean_dec(x_263);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_234, x_9, x_251, x_274, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_275);
lean_dec(x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_252);
lean_dec(x_2);
x_277 = lean_box(0);
x_278 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_234, x_9, x_251, x_277, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_250);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_279 = lean_ctor_get(x_249, 0);
lean_inc(x_279);
lean_dec(x_249);
x_280 = lean_ctor_get(x_247, 1);
lean_inc(x_280);
lean_dec(x_247);
x_281 = lean_ctor_get(x_248, 1);
lean_inc(x_281);
lean_dec(x_248);
x_282 = lean_ctor_get(x_279, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_279, 1);
lean_inc(x_283);
lean_dec(x_279);
x_309 = lean_array_get_size(x_282);
x_310 = lean_unsigned_to_nat(0u);
x_311 = lean_nat_dec_lt(x_310, x_309);
lean_dec(x_309);
if (x_311 == 0)
{
lean_dec(x_282);
x_284 = x_241;
goto block_308;
}
else
{
lean_object* x_312; 
lean_dec(x_241);
x_312 = lean_array_fget(x_282, x_310);
lean_dec(x_282);
x_284 = x_312;
goto block_308;
}
block_308:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_285 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_237, x_18, x_19, x_280);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_286);
x_289 = l_Lean_MVarId_rename(x_283, x_284, x_286, x_16, x_17, x_18, x_19, x_287);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
lean_inc(x_290);
if (lean_is_scalar(x_288)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_288;
 lean_ctor_set_tag(x_292, 1);
}
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_4);
x_293 = l_Lean_Elab_Tactic_setGoals(x_292, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_291);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
lean_inc(x_290);
x_295 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___boxed), 14, 5);
lean_closure_set(x_295, 0, x_290);
lean_closure_set(x_295, 1, x_286);
lean_closure_set(x_295, 2, x_2);
lean_closure_set(x_295, 3, x_10);
lean_closure_set(x_295, 4, x_3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_296 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_290, x_295, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_294);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_234, x_9, x_281, x_297, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_298);
lean_dec(x_297);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_281);
lean_dec(x_234);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_300 = lean_ctor_get(x_296, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_296, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_302 = x_296;
} else {
 lean_dec_ref(x_296);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_288);
lean_dec(x_286);
lean_dec(x_281);
lean_dec(x_234);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = lean_ctor_get(x_289, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_289, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_306 = x_289;
} else {
 lean_dec_ref(x_289);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_241);
lean_dec(x_234);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_313 = lean_ctor_get(x_247, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_247, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_315 = x_247;
} else {
 lean_dec_ref(x_247);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_234);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_317 = lean_ctor_get(x_238, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_238, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_319 = x_238;
} else {
 lean_dec_ref(x_238);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_321 = !lean_is_exclusive(x_24);
if (x_321 == 0)
{
return x_24;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_24, 0);
x_323 = lean_ctor_get(x_24, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_24);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_21);
if (x_325 == 0)
{
return x_21;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_21, 0);
x_327 = lean_ctor_get(x_21, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_21);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("this", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("occurs check failed, expression", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ncontains the goal ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
x_25 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__2;
x_26 = l_Lean_LocalContext_findFromUserName_x3f(x_24, x_25);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_27 = l_Lean_MVarId_assumption(x_9, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_28);
lean_dec(x_8);
lean_dec(x_3);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = l_Lean_LocalDecl_fvarId(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
x_37 = lean_array_mk(x_36);
x_38 = 0;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_10);
x_39 = l_Lean_Meta_simpGoal(x_9, x_12, x_13, x_14, x_38, x_37, x_10, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_40);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_42);
lean_dec(x_8);
lean_dec(x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_48 = l_Lean_MVarId_assumption(x_47, x_19, x_20, x_21, x_22, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_46, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_49);
lean_dec(x_8);
lean_dec(x_3);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_7, 0);
lean_inc(x_59);
x_60 = lean_box(x_6);
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___boxed), 18, 8);
lean_closure_set(x_61, 0, x_1);
lean_closure_set(x_61, 1, x_2);
lean_closure_set(x_61, 2, x_3);
lean_closure_set(x_61, 3, x_4);
lean_closure_set(x_61, 4, x_5);
lean_closure_set(x_61, 5, x_60);
lean_closure_set(x_61, 6, x_7);
lean_closure_set(x_61, 7, x_8);
x_62 = lean_st_ref_get(x_20, x_23);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = 1;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_70 = l_Lean_Elab_Tactic_elabTerm(x_59, x_68, x_69, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_71);
x_73 = l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3(x_9, x_71, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
uint8_t x_76; 
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_77 = lean_ctor_get(x_73, 1);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = l_Lean_indentExpr(x_71);
x_80 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4;
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_79);
lean_ctor_set(x_73, 0, x_80);
x_81 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_81);
lean_ctor_set(x_62, 0, x_73);
x_82 = l_Lean_Expr_mvar___override(x_9);
x_83 = l_Lean_MessageData_ofExpr(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_62);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_86, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_77);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_92 = lean_ctor_get(x_73, 1);
lean_inc(x_92);
lean_dec(x_73);
x_93 = l_Lean_indentExpr(x_71);
x_94 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6;
lean_ctor_set_tag(x_62, 7);
lean_ctor_set(x_62, 1, x_96);
lean_ctor_set(x_62, 0, x_95);
x_97 = l_Lean_Expr_mvar___override(x_9);
x_98 = l_Lean_MessageData_ofExpr(x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_62);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_101, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_92);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_free_object(x_62);
x_107 = lean_ctor_get(x_73, 1);
lean_inc(x_107);
lean_dec(x_73);
x_108 = lean_box(0);
x_109 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10(x_9, x_71, x_68, x_11, x_12, x_13, x_14, x_10, x_61, x_67, x_108, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_107);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_67);
lean_free_object(x_62);
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
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
x_110 = !lean_is_exclusive(x_70);
if (x_110 == 0)
{
return x_70;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_70, 0);
x_112 = lean_ctor_get(x_70, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_70);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_62, 0);
x_115 = lean_ctor_get(x_62, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_62);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_116, 2);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_box(0);
x_119 = 1;
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_120 = l_Lean_Elab_Tactic_elabTerm(x_59, x_118, x_119, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_115);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_121);
x_123 = l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3(x_9, x_121, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_117);
lean_dec(x_61);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = l_Lean_indentExpr(x_121);
x_129 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4;
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(7, 2, 0);
} else {
 x_130 = x_127;
 lean_ctor_set_tag(x_130, 7);
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Expr_mvar___override(x_9);
x_134 = l_Lean_MessageData_ofExpr(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_137, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_126);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
lean_dec(x_123);
x_144 = lean_box(0);
x_145 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10(x_9, x_121, x_118, x_11, x_12, x_13, x_14, x_10, x_61, x_117, x_144, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_117);
lean_dec(x_61);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
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
x_146 = lean_ctor_get(x_120, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_120, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_148 = x_120;
} else {
 lean_dec_ref(x_120);
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
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__6;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__5;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__3;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__7;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__4;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try 'simp' instead of 'simpa'", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__11;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Tactic_getMainGoal(x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = 1;
x_26 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__1;
x_27 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__9;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Meta_simpGoal(x_22, x_1, x_2, x_11, x_25, x_26, x_27, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_28, 1);
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_18, 2);
lean_inc(x_34);
x_35 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
x_36 = l_Lean_Linter_getLinterValue(x_35, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_37 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8;
lean_ctor_set(x_28, 0, x_37);
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_free_object(x_28);
x_38 = lean_ctor_get(x_18, 5);
lean_inc(x_38);
x_39 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__12;
x_40 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(x_35, x_38, x_39, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8;
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_ctor_get(x_18, 2);
lean_inc(x_48);
x_49 = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1;
x_50 = l_Lean_Linter_getLinterValue(x_49, x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_51 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_18, 5);
lean_inc(x_53);
x_54 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__12;
x_55 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(x_49, x_53, x_54, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_47);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_53);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8;
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_30, 0);
lean_inc(x_60);
lean_dec(x_30);
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_dec(x_28);
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_dec(x_29);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_box(x_8);
lean_inc(x_63);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___boxed), 23, 14);
lean_closure_set(x_65, 0, x_3);
lean_closure_set(x_65, 1, x_4);
lean_closure_set(x_65, 2, x_5);
lean_closure_set(x_65, 3, x_6);
lean_closure_set(x_65, 4, x_7);
lean_closure_set(x_65, 5, x_64);
lean_closure_set(x_65, 6, x_9);
lean_closure_set(x_65, 7, x_10);
lean_closure_set(x_65, 8, x_63);
lean_closure_set(x_65, 9, x_62);
lean_closure_set(x_65, 10, x_24);
lean_closure_set(x_65, 11, x_1);
lean_closure_set(x_65, 12, x_2);
lean_closure_set(x_65, 13, x_11);
x_66 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_63, x_65, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_61);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_19);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_28);
if (x_67 == 0)
{
return x_28;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_28, 0);
x_69 = lean_ctor_get(x_28, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_28);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_19);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_21);
if (x_71 == 0)
{
return x_21;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = lean_ctor_get(x_18, 5);
lean_inc(x_171);
x_172 = 0;
x_173 = l_Lean_SourceInfo_fromRef(x_171, x_172);
lean_dec(x_171);
x_174 = lean_st_ref_get(x_19, x_20);
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_174, 1);
x_177 = lean_ctor_get(x_174, 0);
lean_dec(x_177);
x_178 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1;
lean_inc(x_173);
lean_ctor_set_tag(x_174, 2);
lean_ctor_set(x_174, 1, x_178);
lean_ctor_set(x_174, 0, x_173);
x_179 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3;
x_180 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
lean_inc(x_173);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_179);
lean_ctor_set(x_181, 2, x_180);
if (lean_obj_tag(x_11) == 0)
{
x_182 = x_180;
goto block_225;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_11, 0);
lean_inc(x_226);
lean_dec(x_11);
x_227 = lean_array_push(x_180, x_226);
x_182 = x_227;
goto block_225;
}
block_225:
{
lean_object* x_183; lean_object* x_184; 
x_183 = l_Array_append___rarg(x_180, x_182);
lean_dec(x_182);
lean_inc(x_173);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_173);
lean_ctor_set(x_184, 1, x_179);
lean_ctor_set(x_184, 2, x_183);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_173);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_173);
lean_ctor_set(x_186, 1, x_179);
lean_ctor_set(x_186, 2, x_185);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
lean_inc(x_186);
x_188 = l_Lean_Syntax_node6(x_173, x_187, x_174, x_10, x_184, x_186, x_186, x_181);
x_21 = x_188;
x_22 = x_176;
goto block_170;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_189 = lean_ctor_get(x_9, 0);
x_190 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_173);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_173);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Array_append___rarg(x_180, x_189);
lean_inc(x_173);
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_173);
lean_ctor_set(x_193, 1, x_179);
lean_ctor_set(x_193, 2, x_192);
x_194 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_173);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_173);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Array_mkArray3___rarg(x_191, x_193, x_195);
x_197 = l_Array_append___rarg(x_180, x_196);
lean_dec(x_196);
lean_inc(x_173);
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_173);
lean_ctor_set(x_198, 1, x_179);
lean_ctor_set(x_198, 2, x_197);
x_199 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
x_200 = l_Lean_Syntax_node6(x_173, x_199, x_174, x_10, x_184, x_186, x_198, x_181);
x_21 = x_200;
x_22 = x_176;
goto block_170;
}
}
else
{
lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_8, 0);
x_202 = 1;
x_203 = l_Lean_SourceInfo_fromRef(x_201, x_202);
x_204 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14;
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Array_mkArray1___rarg(x_205);
x_207 = l_Array_append___rarg(x_180, x_206);
lean_dec(x_206);
lean_inc(x_173);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_173);
lean_ctor_set(x_208, 1, x_179);
lean_ctor_set(x_208, 2, x_207);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_173);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_173);
lean_ctor_set(x_210, 1, x_179);
lean_ctor_set(x_210, 2, x_209);
x_211 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
x_212 = l_Lean_Syntax_node6(x_173, x_211, x_174, x_10, x_184, x_208, x_210, x_181);
x_21 = x_212;
x_22 = x_176;
goto block_170;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_213 = lean_ctor_get(x_9, 0);
x_214 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_173);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_173);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_Array_append___rarg(x_180, x_213);
lean_inc(x_173);
x_217 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_217, 0, x_173);
lean_ctor_set(x_217, 1, x_179);
lean_ctor_set(x_217, 2, x_216);
x_218 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_173);
x_219 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_219, 0, x_173);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Array_mkArray3___rarg(x_215, x_217, x_219);
x_221 = l_Array_append___rarg(x_180, x_220);
lean_dec(x_220);
lean_inc(x_173);
x_222 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_222, 0, x_173);
lean_ctor_set(x_222, 1, x_179);
lean_ctor_set(x_222, 2, x_221);
x_223 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
x_224 = l_Lean_Syntax_node6(x_173, x_223, x_174, x_10, x_184, x_208, x_222, x_181);
x_21 = x_224;
x_22 = x_176;
goto block_170;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_228 = lean_ctor_get(x_174, 1);
lean_inc(x_228);
lean_dec(x_174);
x_229 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1;
lean_inc(x_173);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_173);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3;
x_232 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4;
lean_inc(x_173);
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_173);
lean_ctor_set(x_233, 1, x_231);
lean_ctor_set(x_233, 2, x_232);
if (lean_obj_tag(x_11) == 0)
{
x_234 = x_232;
goto block_277;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_11, 0);
lean_inc(x_278);
lean_dec(x_11);
x_279 = lean_array_push(x_232, x_278);
x_234 = x_279;
goto block_277;
}
block_277:
{
lean_object* x_235; lean_object* x_236; 
x_235 = l_Array_append___rarg(x_232, x_234);
lean_dec(x_234);
lean_inc(x_173);
x_236 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_236, 0, x_173);
lean_ctor_set(x_236, 1, x_231);
lean_ctor_set(x_236, 2, x_235);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_173);
x_238 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_238, 0, x_173);
lean_ctor_set(x_238, 1, x_231);
lean_ctor_set(x_238, 2, x_237);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
lean_inc(x_238);
x_240 = l_Lean_Syntax_node6(x_173, x_239, x_230, x_10, x_236, x_238, x_238, x_233);
x_21 = x_240;
x_22 = x_228;
goto block_170;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_241 = lean_ctor_get(x_9, 0);
x_242 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_173);
x_243 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_243, 0, x_173);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Array_append___rarg(x_232, x_241);
lean_inc(x_173);
x_245 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_245, 0, x_173);
lean_ctor_set(x_245, 1, x_231);
lean_ctor_set(x_245, 2, x_244);
x_246 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_173);
x_247 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_247, 0, x_173);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Array_mkArray3___rarg(x_243, x_245, x_247);
x_249 = l_Array_append___rarg(x_232, x_248);
lean_dec(x_248);
lean_inc(x_173);
x_250 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_250, 0, x_173);
lean_ctor_set(x_250, 1, x_231);
lean_ctor_set(x_250, 2, x_249);
x_251 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
x_252 = l_Lean_Syntax_node6(x_173, x_251, x_230, x_10, x_236, x_238, x_250, x_233);
x_21 = x_252;
x_22 = x_228;
goto block_170;
}
}
else
{
lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_253 = lean_ctor_get(x_8, 0);
x_254 = 1;
x_255 = l_Lean_SourceInfo_fromRef(x_253, x_254);
x_256 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14;
x_257 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Array_mkArray1___rarg(x_257);
x_259 = l_Array_append___rarg(x_232, x_258);
lean_dec(x_258);
lean_inc(x_173);
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_173);
lean_ctor_set(x_260, 1, x_231);
lean_ctor_set(x_260, 2, x_259);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5;
lean_inc(x_173);
x_262 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_262, 0, x_173);
lean_ctor_set(x_262, 1, x_231);
lean_ctor_set(x_262, 2, x_261);
x_263 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
x_264 = l_Lean_Syntax_node6(x_173, x_263, x_230, x_10, x_236, x_260, x_262, x_233);
x_21 = x_264;
x_22 = x_228;
goto block_170;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_265 = lean_ctor_get(x_9, 0);
x_266 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12;
lean_inc(x_173);
x_267 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_267, 0, x_173);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Array_append___rarg(x_232, x_265);
lean_inc(x_173);
x_269 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_269, 0, x_173);
lean_ctor_set(x_269, 1, x_231);
lean_ctor_set(x_269, 2, x_268);
x_270 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13;
lean_inc(x_173);
x_271 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_271, 0, x_173);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Array_mkArray3___rarg(x_267, x_269, x_271);
x_273 = l_Array_append___rarg(x_232, x_272);
lean_dec(x_272);
lean_inc(x_173);
x_274 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_274, 0, x_173);
lean_ctor_set(x_274, 1, x_231);
lean_ctor_set(x_274, 2, x_273);
x_275 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2;
x_276 = l_Lean_Syntax_node6(x_173, x_275, x_230, x_10, x_236, x_260, x_274, x_233);
x_21 = x_276;
x_22 = x_228;
goto block_170;
}
}
}
}
block_170:
{
uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = 0;
x_24 = 0;
x_25 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___closed__1;
x_26 = lean_box(x_23);
x_27 = lean_box(x_24);
x_28 = lean_box(x_23);
lean_inc(x_21);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_29, 0, x_21);
lean_closure_set(x_29, 1, x_26);
lean_closure_set(x_29, 2, x_27);
lean_closure_set(x_29, 3, x_28);
lean_closure_set(x_29, 4, x_25);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_30 = l_Lean_Elab_Tactic_withMainContext___rarg(x_29, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
if (lean_obj_tag(x_7) == 0)
{
x_36 = x_23;
goto block_164;
}
else
{
uint8_t x_165; 
x_165 = 1;
x_36 = x_165;
goto block_164;
}
block_164:
{
uint8_t x_37; 
if (x_36 == 0)
{
x_37 = x_23;
goto block_162;
}
else
{
uint8_t x_163; 
x_163 = 1;
x_37 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_33;
goto block_103;
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_33);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_33, 0);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = 1;
lean_ctor_set_uint8(x_105, sizeof(void*)*2 + 11, x_107);
x_38 = x_33;
goto block_103;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
x_110 = lean_ctor_get_uint8(x_105, sizeof(void*)*2);
x_111 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 1);
x_112 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 2);
x_113 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 3);
x_114 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 4);
x_115 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 5);
x_116 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 6);
x_117 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 7);
x_118 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 8);
x_119 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 9);
x_120 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 10);
x_121 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 12);
x_122 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 13);
x_123 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 14);
x_124 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 15);
x_125 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 16);
x_126 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 17);
x_127 = lean_ctor_get_uint8(x_105, sizeof(void*)*2 + 18);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_105);
x_128 = 1;
x_129 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_129, 0, x_108);
lean_ctor_set(x_129, 1, x_109);
lean_ctor_set_uint8(x_129, sizeof(void*)*2, x_110);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 1, x_111);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 2, x_112);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 3, x_113);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 4, x_114);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 5, x_115);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 6, x_116);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 7, x_117);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 8, x_118);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 9, x_119);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 10, x_120);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 11, x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 12, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 13, x_122);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 14, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 15, x_124);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 16, x_125);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 17, x_126);
lean_ctor_set_uint8(x_129, sizeof(void*)*2 + 18, x_127);
lean_ctor_set(x_33, 0, x_129);
x_38 = x_33;
goto block_103;
}
}
else
{
lean_object* x_130; uint32_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint32_t x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; 
x_130 = lean_ctor_get(x_33, 0);
x_131 = lean_ctor_get_uint32(x_33, sizeof(void*)*5);
x_132 = lean_ctor_get(x_33, 1);
x_133 = lean_ctor_get(x_33, 2);
x_134 = lean_ctor_get(x_33, 3);
x_135 = lean_ctor_get_uint32(x_33, sizeof(void*)*5 + 4);
x_136 = lean_ctor_get(x_33, 4);
x_137 = lean_ctor_get_uint8(x_33, sizeof(void*)*5 + 8);
lean_inc(x_136);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_130);
lean_dec(x_33);
x_138 = lean_ctor_get(x_130, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_130, 1);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_130, sizeof(void*)*2);
x_141 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 1);
x_142 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 2);
x_143 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 3);
x_144 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 4);
x_145 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 5);
x_146 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 6);
x_147 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 7);
x_148 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 8);
x_149 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 9);
x_150 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 10);
x_151 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 12);
x_152 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 13);
x_153 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 14);
x_154 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 15);
x_155 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 16);
x_156 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 17);
x_157 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 18);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_158 = x_130;
} else {
 lean_dec_ref(x_130);
 x_158 = lean_box(0);
}
x_159 = 1;
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 19);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_138);
lean_ctor_set(x_160, 1, x_139);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_140);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 1, x_141);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 2, x_142);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 3, x_143);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 4, x_144);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 5, x_145);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 6, x_146);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 7, x_147);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 8, x_148);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 9, x_149);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 10, x_150);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 11, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 12, x_151);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 13, x_152);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 14, x_153);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 15, x_154);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 16, x_155);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 17, x_156);
lean_ctor_set_uint8(x_160, sizeof(void*)*2 + 18, x_157);
x_161 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_132);
lean_ctor_set(x_161, 2, x_133);
lean_ctor_set(x_161, 3, x_134);
lean_ctor_set(x_161, 4, x_136);
lean_ctor_set_uint32(x_161, sizeof(void*)*5, x_131);
lean_ctor_set_uint32(x_161, sizeof(void*)*5 + 4, x_135);
lean_ctor_set_uint8(x_161, sizeof(void*)*5 + 8, x_137);
x_38 = x_161;
goto block_103;
}
}
block_103:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 13, x_23);
x_42 = lean_box(x_37);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___boxed), 20, 10);
lean_closure_set(x_43, 0, x_38);
lean_closure_set(x_43, 1, x_34);
lean_closure_set(x_43, 2, x_21);
lean_closure_set(x_43, 3, x_1);
lean_closure_set(x_43, 4, x_2);
lean_closure_set(x_43, 5, x_3);
lean_closure_set(x_43, 6, x_4);
lean_closure_set(x_43, 7, x_42);
lean_closure_set(x_43, 8, x_5);
lean_closure_set(x_43, 9, x_6);
x_44 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(x_35, x_43, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
lean_dec(x_35);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
x_47 = lean_ctor_get_uint8(x_40, sizeof(void*)*2);
x_48 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 1);
x_49 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 2);
x_50 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 3);
x_51 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 4);
x_52 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 5);
x_53 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 6);
x_54 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 7);
x_55 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 8);
x_56 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 9);
x_57 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 10);
x_58 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 11);
x_59 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 12);
x_60 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 14);
x_61 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 15);
x_62 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 16);
x_63 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 17);
x_64 = lean_ctor_get_uint8(x_40, sizeof(void*)*2 + 18);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_65 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_65, 0, x_45);
lean_ctor_set(x_65, 1, x_46);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_47);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 1, x_48);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 2, x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 3, x_50);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 4, x_51);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 5, x_52);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 6, x_53);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 7, x_54);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 8, x_55);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 9, x_56);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 10, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 11, x_58);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 12, x_59);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 13, x_23);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 14, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 15, x_61);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 17, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 18, x_64);
lean_ctor_set(x_38, 0, x_65);
x_66 = lean_box(x_37);
x_67 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___boxed), 20, 10);
lean_closure_set(x_67, 0, x_38);
lean_closure_set(x_67, 1, x_34);
lean_closure_set(x_67, 2, x_21);
lean_closure_set(x_67, 3, x_1);
lean_closure_set(x_67, 4, x_2);
lean_closure_set(x_67, 5, x_3);
lean_closure_set(x_67, 6, x_4);
lean_closure_set(x_67, 7, x_66);
lean_closure_set(x_67, 8, x_5);
lean_closure_set(x_67, 9, x_6);
x_68 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(x_35, x_67, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
lean_dec(x_35);
return x_68;
}
}
else
{
lean_object* x_69; uint32_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint32_t x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_69 = lean_ctor_get(x_38, 0);
x_70 = lean_ctor_get_uint32(x_38, sizeof(void*)*5);
x_71 = lean_ctor_get(x_38, 1);
x_72 = lean_ctor_get(x_38, 2);
x_73 = lean_ctor_get(x_38, 3);
x_74 = lean_ctor_get_uint32(x_38, sizeof(void*)*5 + 4);
x_75 = lean_ctor_get(x_38, 4);
x_76 = lean_ctor_get_uint8(x_38, sizeof(void*)*5 + 8);
lean_inc(x_75);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_dec(x_38);
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_69, sizeof(void*)*2);
x_80 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 1);
x_81 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 2);
x_82 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 3);
x_83 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 4);
x_84 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 5);
x_85 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 6);
x_86 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 7);
x_87 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 8);
x_88 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 9);
x_89 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 10);
x_90 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 11);
x_91 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 12);
x_92 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 14);
x_93 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 15);
x_94 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 16);
x_95 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 17);
x_96 = lean_ctor_get_uint8(x_69, sizeof(void*)*2 + 18);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_97 = x_69;
} else {
 lean_dec_ref(x_69);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 19);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_79);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 1, x_80);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 2, x_81);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 3, x_82);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 4, x_83);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 5, x_84);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 6, x_85);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 7, x_86);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 8, x_87);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 9, x_88);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 10, x_89);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 11, x_90);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 12, x_91);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 13, x_23);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 14, x_92);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 15, x_93);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 16, x_94);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 17, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2 + 18, x_96);
x_99 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_71);
lean_ctor_set(x_99, 2, x_72);
lean_ctor_set(x_99, 3, x_73);
lean_ctor_set(x_99, 4, x_75);
lean_ctor_set_uint32(x_99, sizeof(void*)*5, x_70);
lean_ctor_set_uint32(x_99, sizeof(void*)*5 + 4, x_74);
lean_ctor_set_uint8(x_99, sizeof(void*)*5 + 8, x_76);
x_100 = lean_box(x_37);
x_101 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___boxed), 20, 10);
lean_closure_set(x_101, 0, x_99);
lean_closure_set(x_101, 1, x_34);
lean_closure_set(x_101, 2, x_21);
lean_closure_set(x_101, 3, x_1);
lean_closure_set(x_101, 4, x_2);
lean_closure_set(x_101, 5, x_3);
lean_closure_set(x_101, 6, x_4);
lean_closure_set(x_101, 7, x_100);
lean_closure_set(x_101, 8, x_5);
lean_closure_set(x_101, 9, x_6);
x_102 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(x_35, x_101, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_32);
lean_dec(x_35);
return x_102;
}
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_30);
if (x_166 == 0)
{
return x_30;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_30, 0);
x_168 = lean_ctor_get(x_30, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_30);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Syntax_getOptional_x3f(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_28; 
x_28 = lean_box(0);
x_23 = x_28;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
x_23 = x_22;
goto block_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_23 = x_31;
goto block_27;
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___boxed), 20, 11);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_3);
lean_closure_set(x_24, 2, x_4);
lean_closure_set(x_24, 3, x_5);
lean_closure_set(x_24, 4, x_12);
lean_closure_set(x_24, 5, x_6);
lean_closure_set(x_24, 6, x_7);
lean_closure_set(x_24, 7, x_8);
lean_closure_set(x_24, 8, x_9);
lean_closure_set(x_24, 9, x_10);
lean_closure_set(x_24, 10, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_Tactic_focus___rarg(x_25, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(4u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = l_Lean_Syntax_isNone(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(2u);
lean_inc(x_23);
x_26 = l_Lean_Syntax_matchesNull(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = l_Lean_Syntax_getArg(x_23, x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__14(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_10, x_31, x_30, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__14(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_10, x_34, x_33, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_22);
x_25 = l_Lean_Syntax_matchesNull(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_22, x_27);
lean_dec(x_22);
x_29 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11;
lean_inc(x_28);
x_30 = l_Lean_Syntax_isOfKind(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_20);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_Syntax_getArg(x_28, x_24);
lean_dec(x_28);
x_33 = l_Lean_Syntax_getArgs(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_9, x_35, x_34, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_22);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_9, x_38, x_37, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_39;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpaArgsRest", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__2;
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_17, x_21);
x_23 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__4;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_Lean_Syntax_getArg(x_17, x_26);
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_17, x_28);
x_30 = l_Lean_Syntax_isNone(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_inc(x_29);
x_31 = l_Lean_Syntax_matchesNull(x_29, x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_15);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Lean_Syntax_getArg(x_29, x_21);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__16(x_17, x_27, x_2, x_23, x_18, x_3, x_4, x_6, x_22, x_35, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_27);
lean_dec(x_17);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__16(x_17, x_27, x_2, x_23, x_18, x_3, x_4, x_6, x_22, x_38, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_27);
lean_dec(x_17);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_19 = l_Lean_Syntax_matchesNull(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
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
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_16, x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17(x_1, x_2, x_3, x_5, x_24, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17(x_1, x_2, x_3, x_5, x_27, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
x_2 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
x_4 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_inc(x_17);
x_19 = l_Lean_Syntax_matchesNull(x_17, x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_Syntax_getArg(x_17, x_14);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__18(x_1, x_15, x_11, x_23, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__18(x_1, x_15, x_11, x_26, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_getDelayedMVarAssignment_x3f___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_occursCheck_visit___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___boxed(lean_object** _args) {
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
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_9);
lean_dec(x_9);
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__5___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_8);
lean_dec(x_8);
x_21 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___boxed(lean_object** _args) {
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
x_21 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_11);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_24; lean_object* x_25; 
x_24 = lean_unbox(x_6);
lean_dec(x_6);
x_25 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11(x_1, x_2, x_3, x_4, x_5, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___boxed(lean_object** _args) {
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
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_8);
lean_dec(x_8);
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___boxed(lean_object** _args) {
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
x_21 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__14___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_11);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__15___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__16___boxed(lean_object** _args) {
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
x_21 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simpa", 5, 5);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpa", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simpa_evalSimpa), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__5;
x_3 = l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(90u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(43u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(33u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(56u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__7;
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
l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__1 = _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__1();
lean_mark_persistent(l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__1);
l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__2 = _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__2();
lean_mark_persistent(l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__2);
l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__3 = _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__3();
lean_mark_persistent(l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__3);
l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__4 = _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__4();
lean_mark_persistent(l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__4);
l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__5 = _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__5();
lean_mark_persistent(l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__5);
l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__6 = _init_l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__6();
lean_mark_persistent(l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4____closed__6);
res = l_initFn____x40_Lean_Elab_Tactic_Simpa___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_linter_unnecessarySimpa = lean_io_result_get_value(res);
lean_mark_persistent(l_linter_unnecessarySimpa);
lean_dec_ref(res);
l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___closed__1);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__1 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__1);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__2 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__2);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__3);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__4 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__4);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__5 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__5);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__6);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__7 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__7);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__8 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__8);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__9 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__9);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__10 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__10);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__11 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__11);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__12 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__12);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__13 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__13);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__14 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__14);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__15 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__15);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__16 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__16();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__16);
l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__17 = _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__17();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_reprUseImplicitLambdaResult____x40_Lean_Elab_Tactic_Simpa___hyg_51____closed__17);
l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult___closed__1);
l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult = _init_l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_instReprUseImplicitLambdaResult);
l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__1 = _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__1();
lean_mark_persistent(l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__1);
l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__2 = _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__2();
lean_mark_persistent(l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__2);
l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__3 = _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__3();
lean_mark_persistent(l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__3);
l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__4 = _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__4();
lean_mark_persistent(l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__4);
l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5 = _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5();
lean_mark_persistent(l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__5);
l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__6 = _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__6();
lean_mark_persistent(l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__6);
l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__7 = _init_l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__7();
lean_mark_persistent(l_Lean_Linter_logLint___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__1___closed__7);
l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2___closed__1 = _init_l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__2___closed__1);
l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1 = _init_l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__1);
l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__2 = _init_l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__2();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__5___closed__2);
l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__1 = _init_l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__1();
lean_mark_persistent(l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__1);
l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__2 = _init_l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__2();
lean_mark_persistent(l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__2);
l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__3 = _init_l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__3();
lean_mark_persistent(l_Lean_occursCheck___at_Lean_Elab_Tactic_Simpa_evalSimpa___spec__3___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__3___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__9);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__10 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__10);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__11);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__12);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__13);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__14);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__15 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__15);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__16);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__17 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__17);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__18 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__18);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__19 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__19);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__20 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__20);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__4___closed__21);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__6___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__8___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__9___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__10___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__11___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__5 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__5);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__6 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__6);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__7 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__7);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__8);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__9 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__9);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__10 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__10);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__11 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__11);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__12 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__12___closed__12);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__13___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__1);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__2 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__2);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__3 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__3);
l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__4 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___lambda__17___closed__4);
l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1 = _init_l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Simpa_evalSimpa___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
