// Lean compiler output
// Module: Lean.Elab.Tactic.Simp
// Imports: Lean.Meta.Tactic.Simp Lean.Meta.Tactic.Replace Lean.Elab.BuiltinNotation Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Location Lean.Elab.Tactic.Config
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
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__3;
static lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__4;
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__8;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1(lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__4;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__7;
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__6;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2;
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3;
uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instBEqSimpKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__4;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
uint8_t l_Lean_LocalDecl_hasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__1;
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__5;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8;
static lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5;
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__7;
uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__2;
uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__1;
lean_object* l_Lean_Meta_Simp_getSimprocs___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__4;
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__3;
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__1(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_traceSimpCall___closed__1;
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion(lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_UsedSimps_toArray(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1(lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__14;
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__5;
uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__5;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__9;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__2;
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__1;
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__6;
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__4;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_elabSimpArgs___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1;
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__13;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_instInhabitedSimpKind;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__1;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx___boxed(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx(uint8_t);
static lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__2;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
static lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3;
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__3;
lean_object* l_Lean_Meta_abstractMVars(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4;
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__1;
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_rootNamespace;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__1;
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__1;
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__1;
static lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__5;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1;
lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__6;
static lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__9;
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__3;
lean_object* l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__5;
static lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2;
static lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_reportDiag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__7;
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__5;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at_Lean_Elab_Tactic_tacticToDischarge___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___lambda__1(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__6;
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__5;
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3;
uint8_t lean_is_inaccessible_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__3;
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__1;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_Origin_converse(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instBEqSimpKind;
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__8;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__1;
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__3;
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__4;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__6;
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__4;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8;
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__4;
static lean_object* l_Lean_Elab_Tactic_traceSimpCall___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__2;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Config", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2;
x_3 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__3;
x_4 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5;
x_10 = 0;
x_11 = l_Lean_Meta_evalExpr_x27___rarg(x_9, x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
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
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_22 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Exception_toMessageData(x_16);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCore___spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_41 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Exception_toMessageData(x_35);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCore___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasSorry(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5;
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
x_18 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2(x_14, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
x_19 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1;
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
x_24 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2(x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
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
x_25 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__4;
x_2 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5;
x_16 = l_Lean_Environment_contains(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__5;
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
x_24 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_getConfigItems(x_1);
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
x_19 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4(x_11, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_37 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4(x_11, x_13, x_36, x_4, x_5, x_6, x_7, x_35, x_9, x_10);
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
x_38 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpConfigCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ConfigCtx", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2;
x_3 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__3;
x_4 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2;
x_10 = 0;
x_11 = l_Lean_Meta_evalExpr_x27___rarg(x_9, x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_22 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Exception_toMessageData(x_16);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_41 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Exception_toMessageData(x_35);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasSorry(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 1;
x_4 = 0;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2;
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
x_18 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__2(x_14, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
x_19 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1;
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
x_24 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__2(x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
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
x_25 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__1;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2;
x_16 = l_Lean_Environment_contains(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__3;
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
x_24 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_getConfigItems(x_1);
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
x_19 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4(x_11, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_37 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4(x_11, x_13, x_36, x_4, x_5, x_6, x_7, x_35, x_9, x_10);
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
x_38 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DSimp", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2;
x_3 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__1;
x_4 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2;
x_10 = 0;
x_11 = l_Lean_Meta_evalExpr_x27___rarg(x_9, x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146_(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_22 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Exception_toMessageData(x_16);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_41 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Exception_toMessageData(x_35);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasSorry(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
lean_ctor_set_uint8(x_4, 4, x_1);
lean_ctor_set_uint8(x_4, 5, x_1);
lean_ctor_set_uint8(x_4, 6, x_3);
lean_ctor_set_uint8(x_4, 7, x_3);
lean_ctor_set_uint8(x_4, 8, x_1);
lean_ctor_set_uint8(x_4, 9, x_3);
lean_ctor_set_uint8(x_4, 10, x_3);
lean_ctor_set_uint8(x_4, 11, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2;
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
x_18 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__2(x_14, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
x_19 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1;
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
x_24 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__2(x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
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
x_25 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__1;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2;
x_16 = l_Lean_Environment_contains(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__3;
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
x_24 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_getConfigItems(x_1);
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
x_19 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4(x_11, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_37 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4(x_11, x_13, x_36, x_4, x_5, x_6, x_7, x_35, x_9, x_10);
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
x_38 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabDSimpConfigCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Tactic_SimpKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Elab_Tactic_instInhabitedSimpKind() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Elab_Tactic_SimpKind_toCtorIdx(x_1);
x_4 = l_Lean_Elab_Tactic_SimpKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instBEqSimpKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instBEqSimpKind() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instBEqSimpKind___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at_Lean_Elab_Tactic_tacticToDischarge___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Expr_hasExprMVar(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = l_Lean_Expr_hasExprMVar(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at_Lean_Elab_Tactic_tacticToDischarge___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = l_Lean_Exception_isInterrupt(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Exception_isRuntime(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = lean_box(0);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
return x_9;
}
}
else
{
return x_9;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discharger", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__3;
lean_inc(x_8);
x_14 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_4, x_13, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_mvarId_x21(x_15);
x_21 = lean_box(0);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___boxed), 11, 4);
lean_closure_set(x_24, 0, x_20);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_21);
lean_closure_set(x_24, 3, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___lambda__1), 9, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_15);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___lambda__2), 8, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_Lean_Elab_Term_TermElabM_run___rarg(x_26, x_3, x_18, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_st_ref_set(x_1, x_31, x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticTry_", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_tacticToDischarge___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_tacticToDischarge___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_tacticToDischarge___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_tacticToDischarge___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_11, x_12);
x_14 = lean_st_ref_get(x_9, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_Lean_Elab_Tactic_tacticToDischarge___closed__5;
lean_inc(x_13);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_13);
x_19 = l_Lean_Elab_Tactic_tacticToDischarge___closed__14;
lean_inc(x_13);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_tacticToDischarge___closed__15;
lean_inc(x_13);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Tactic_tacticToDischarge___closed__13;
lean_inc(x_13);
x_24 = l_Lean_Syntax_node3(x_13, x_23, x_20, x_1, x_22);
x_25 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_13);
x_26 = l_Lean_Syntax_node1(x_13, x_25, x_24);
x_27 = l_Lean_Elab_Tactic_tacticToDischarge___closed__9;
lean_inc(x_13);
x_28 = l_Lean_Syntax_node1(x_13, x_27, x_26);
x_29 = l_Lean_Elab_Tactic_tacticToDischarge___closed__7;
lean_inc(x_13);
x_30 = l_Lean_Syntax_node1(x_13, x_29, x_28);
x_31 = l_Lean_Elab_Tactic_tacticToDischarge___closed__4;
x_32 = l_Lean_Syntax_node2(x_13, x_31, x_14, x_30);
x_33 = lean_st_ref_get(x_5, x_16);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_st_mk_ref(x_35, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___boxed), 12, 3);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_32);
lean_closure_set(x_40, 2, x_4);
lean_ctor_set(x_33, 1, x_40);
lean_ctor_set(x_33, 0, x_39);
lean_ctor_set(x_37, 0, x_33);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
lean_inc(x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___boxed), 12, 3);
lean_closure_set(x_43, 0, x_41);
lean_closure_set(x_43, 1, x_32);
lean_closure_set(x_43, 2, x_4);
lean_ctor_set(x_33, 1, x_43);
lean_ctor_set(x_33, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_33);
x_47 = lean_st_mk_ref(x_45, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
lean_inc(x_48);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___boxed), 12, 3);
lean_closure_set(x_51, 0, x_48);
lean_closure_set(x_51, 1, x_32);
lean_closure_set(x_51, 2, x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = l_Lean_Elab_Tactic_tacticToDischarge___closed__5;
lean_inc(x_13);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_13);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Elab_Tactic_tacticToDischarge___closed__14;
lean_inc(x_13);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_13);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Tactic_tacticToDischarge___closed__15;
lean_inc(x_13);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_13);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Tactic_tacticToDischarge___closed__13;
lean_inc(x_13);
x_62 = l_Lean_Syntax_node3(x_13, x_61, x_58, x_1, x_60);
x_63 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_13);
x_64 = l_Lean_Syntax_node1(x_13, x_63, x_62);
x_65 = l_Lean_Elab_Tactic_tacticToDischarge___closed__9;
lean_inc(x_13);
x_66 = l_Lean_Syntax_node1(x_13, x_65, x_64);
x_67 = l_Lean_Elab_Tactic_tacticToDischarge___closed__7;
lean_inc(x_13);
x_68 = l_Lean_Syntax_node1(x_13, x_67, x_66);
x_69 = l_Lean_Elab_Tactic_tacticToDischarge___closed__4;
x_70 = l_Lean_Syntax_node2(x_13, x_69, x_56, x_68);
x_71 = lean_st_ref_get(x_5, x_54);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_st_mk_ref(x_72, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
lean_inc(x_76);
x_79 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___boxed), 12, 3);
lean_closure_set(x_79, 0, x_76);
lean_closure_set(x_79, 1, x_70);
lean_closure_set(x_79, 2, x_4);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_74;
}
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_tacticToDischarge(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_apply_10(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_st_ref_get(x_6, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_set(x_14, x_17, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
lean_inc(x_6);
x_22 = lean_apply_10(x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_14, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_set(x_6, x_26, x_27);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_23);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_st_ref_get(x_14, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_set(x_6, x_36, x_37);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_33);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Syntax_isNone(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_13, x_14);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_tacticToDischarge(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 1);
return x_16;
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
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (x_2) {
case 0:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_elabSimpConfigCore(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_elabSimpConfigCtxCore(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
default: 
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_elabDSimpConfigCore(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get_uint8(x_24, 0);
x_26 = lean_ctor_get_uint8(x_24, 1);
x_27 = lean_ctor_get_uint8(x_24, 2);
x_28 = lean_ctor_get_uint8(x_24, 3);
x_29 = lean_ctor_get_uint8(x_24, 4);
x_30 = lean_ctor_get_uint8(x_24, 5);
x_31 = lean_ctor_get_uint8(x_24, 6);
x_32 = lean_ctor_get_uint8(x_24, 7);
x_33 = lean_ctor_get_uint8(x_24, 8);
x_34 = lean_ctor_get_uint8(x_24, 9);
x_35 = lean_ctor_get_uint8(x_24, 10);
x_36 = lean_ctor_get_uint8(x_24, 11);
lean_dec(x_24);
x_37 = l_Lean_Meta_Simp_defaultMaxSteps;
x_38 = lean_unsigned_to_nat(2u);
x_39 = 0;
x_40 = 1;
x_41 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 2, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 3, x_25);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 4, x_26);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 5, x_27);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 6, x_28);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 7, x_29);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 8, x_30);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 9, x_31);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 10, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 11, x_32);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 12, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 13, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 14, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 15, x_34);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 17, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 18, x_40);
lean_ctor_set(x_22, 0, x_41);
return x_22;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_ctor_get_uint8(x_42, 0);
x_45 = lean_ctor_get_uint8(x_42, 1);
x_46 = lean_ctor_get_uint8(x_42, 2);
x_47 = lean_ctor_get_uint8(x_42, 3);
x_48 = lean_ctor_get_uint8(x_42, 4);
x_49 = lean_ctor_get_uint8(x_42, 5);
x_50 = lean_ctor_get_uint8(x_42, 6);
x_51 = lean_ctor_get_uint8(x_42, 7);
x_52 = lean_ctor_get_uint8(x_42, 8);
x_53 = lean_ctor_get_uint8(x_42, 9);
x_54 = lean_ctor_get_uint8(x_42, 10);
x_55 = lean_ctor_get_uint8(x_42, 11);
lean_dec(x_42);
x_56 = l_Lean_Meta_Simp_defaultMaxSteps;
x_57 = lean_unsigned_to_nat(2u);
x_58 = 0;
x_59 = 1;
x_60 = lean_alloc_ctor(0, 2, 19);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 2, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 3, x_44);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 4, x_45);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 5, x_46);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 6, x_47);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 7, x_48);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 8, x_49);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 9, x_50);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 10, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 11, x_51);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 12, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 13, x_52);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 14, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 15, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 16, x_54);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 17, x_55);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 18, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_43);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_22);
if (x_62 == 0)
{
return x_22;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_22, 0);
x_64 = lean_ctor_get(x_22, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_22);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_elabSimpConfig(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; 
x_10 = 2;
x_11 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729_(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Meta_SimpTheorems_addDeclToUnfold(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_2, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid argument, variable is not a proposition or let-declaration", 66, 66);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid '←' modifier, '", 25, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is a let-declaration name to be unfolded", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is a declaration name to be unfolded", 38, 38);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isConst(x_3);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isFVar(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_15 = lean_unsigned_to_nat(1000u);
x_16 = l_Lean_Meta_SimpTheorems_add(x_1, x_2, x_14, x_3, x_5, x_4, x_15, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_fvarId_x21(x_3);
lean_inc(x_7);
lean_inc(x_17);
x_18 = l_Lean_FVarId_getDecl(x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_isProp(x_21, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = l_Lean_LocalDecl_isLet(x_19);
lean_dec(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_29 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__3;
x_30 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(x_29, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_30;
}
else
{
if (x_5 == 0)
{
lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_31 = l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(x_1, x_17);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_22);
lean_dec(x_17);
lean_dec(x_1);
x_32 = l_Lean_MessageData_ofExpr(x_3);
x_33 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__7;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(x_36, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = l_Lean_LocalDecl_isLet(x_19);
lean_dec(x_19);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_40 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__3;
x_41 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(x_40, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_41;
}
else
{
if (x_5 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_42 = l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(x_1, x_17);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_1);
x_44 = l_Lean_MessageData_ofExpr(x_3);
x_45 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__7;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(x_48, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_19);
lean_dec(x_17);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_dec(x_22);
x_51 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_52 = lean_unsigned_to_nat(1000u);
x_53 = l_Lean_Meta_SimpTheorems_add(x_1, x_2, x_51, x_3, x_5, x_4, x_52, x_7, x_8, x_9, x_10, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
return x_22;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_22, 0);
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_22);
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
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_2);
x_62 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
lean_inc(x_62);
x_63 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_62, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_ConstantInfo_type(x_64);
lean_dec(x_64);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_67 = l_Lean_Meta_isProp(x_66, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
if (x_5 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___lambda__1(x_6, x_1, x_62, x_71, x_7, x_8, x_9, x_10, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = l_Lean_MessageData_ofName(x_62);
x_75 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__9;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_78, x_7, x_8, x_9, x_10, x_73);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_67, 1);
lean_inc(x_84);
lean_dec(x_67);
x_85 = lean_unsigned_to_nat(1000u);
x_86 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_62, x_4, x_5, x_85, x_7, x_8, x_9, x_10, x_84);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_67);
if (x_87 == 0)
{
return x_67;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_67, 0);
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_67);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_63);
if (x_91 == 0)
{
return x_63;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_63, 0);
x_93 = lean_ctor_get(x_63, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_63);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_1, x_2, x_3, x_12, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Expr_eta(x_1);
x_11 = l_Lean_Expr_hasMVar(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_16 = 1;
x_17 = l_Lean_Meta_abstractMVars(x_10, x_16, x_5, x_6, x_7, x_8, x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 2);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_13, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_17, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_Expr_hasSyntheticSorry(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_20);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1(x_22, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = l_Lean_Expr_hasSyntheticSorry(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1(x_27, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
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
lean_dec(x_7);
lean_dec(x_8);
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
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
x_43 = lean_ctor_get(x_7, 2);
x_44 = lean_ctor_get(x_7, 3);
x_45 = lean_ctor_get(x_7, 4);
x_46 = lean_ctor_get(x_7, 5);
x_47 = lean_ctor_get(x_7, 6);
x_48 = lean_ctor_get(x_7, 7);
x_49 = lean_ctor_get(x_7, 8);
x_50 = lean_ctor_get(x_7, 9);
x_51 = lean_ctor_get(x_7, 10);
x_52 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_53 = lean_ctor_get(x_7, 11);
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_53);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_7);
x_55 = l_Lean_replaceRef(x_1, x_46);
lean_dec(x_46);
x_56 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_42);
lean_ctor_set(x_56, 2, x_43);
lean_ctor_set(x_56, 3, x_44);
lean_ctor_set(x_56, 4, x_45);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_56, 6, x_47);
lean_ctor_set(x_56, 7, x_48);
lean_ctor_set(x_56, 8, x_49);
lean_ctor_set(x_56, 9, x_50);
lean_ctor_set(x_56, 10, x_51);
lean_ctor_set(x_56, 11, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*12, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*12 + 1, x_54);
x_57 = 1;
lean_inc(x_8);
lean_inc(x_56);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_58 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_57, x_57, x_3, x_4, x_5, x_6, x_56, x_8, x_9);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = 1;
lean_inc(x_8);
lean_inc(x_56);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_62 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_61, x_57, x_3, x_4, x_5, x_6, x_56, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_59, x_3, x_4, x_5, x_6, x_56, x_8, x_63);
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
x_68 = l_Lean_Expr_hasSyntheticSorry(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1(x_65, x_69, x_3, x_4, x_5, x_6, x_56, x_8, x_66);
lean_dec(x_8);
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_58, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_58, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_78 = x_58;
} else {
 lean_dec_ref(x_58);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(0);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__2), 9, 2);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___rarg(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_unsigned_to_nat(1000u);
x_26 = l_Lean_Meta_SimpTheorems_add(x_1, x_2, x_23, x_24, x_5, x_4, x_25, x_8, x_9, x_10, x_11, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_7);
x_8 = l_Lean_Meta_Simp_isSimproc(x_7, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___lambda__1(x_7, x_18, x_2, x_3, x_4, x_5, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__2;
lean_inc(x_1);
x_23 = l_Lean_Syntax_isOfKind(x_1, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_39 = x_25;
} else {
 lean_dec_ref(x_25);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_46 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_102 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__4;
x_103 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_104 = l_Lean_Elab_Term_resolveId_x3f(x_1, x_102, x_103, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_5);
lean_dec(x_4);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_7);
lean_dec(x_6);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_108 = lean_erase_macro_scopes(x_107);
x_109 = l_Lean_Meta_Simp_isBuiltinSimproc(x_108, x_8, x_9, x_106);
lean_dec(x_9);
lean_dec(x_8);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = l_Lean_Meta_getSimpExtension_x3f(x_108, x_112);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_113, 1);
x_117 = l_Lean_Meta_Simp_getSimprocExtension_x3f(x_108, x_116);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_free_object(x_113);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3;
x_11 = x_120;
x_12 = x_119;
goto block_21;
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_117);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_117, 1);
x_123 = lean_ctor_get(x_117, 0);
lean_dec(x_123);
lean_ctor_set_tag(x_117, 3);
lean_ctor_set(x_117, 1, x_118);
lean_ctor_set(x_117, 0, x_115);
x_124 = lean_box(0);
lean_ctor_set(x_113, 1, x_124);
lean_ctor_set(x_113, 0, x_117);
x_11 = x_113;
x_12 = x_122;
goto block_21;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
lean_dec(x_117);
x_126 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_126, 0, x_115);
lean_ctor_set(x_126, 1, x_118);
x_127 = lean_box(0);
lean_ctor_set(x_113, 1, x_127);
lean_ctor_set(x_113, 0, x_126);
x_11 = x_113;
x_12 = x_125;
goto block_21;
}
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_117);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_117, 0);
x_130 = lean_ctor_get(x_117, 1);
lean_ctor_set_tag(x_117, 3);
lean_ctor_set(x_117, 1, x_129);
lean_ctor_set(x_117, 0, x_115);
x_131 = lean_box(0);
lean_ctor_set(x_113, 1, x_131);
lean_ctor_set(x_113, 0, x_117);
x_11 = x_113;
x_12 = x_130;
goto block_21;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_117, 0);
x_133 = lean_ctor_get(x_117, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_117);
x_134 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_134, 0, x_115);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_box(0);
lean_ctor_set(x_113, 1, x_135);
lean_ctor_set(x_113, 0, x_134);
x_11 = x_113;
x_12 = x_133;
goto block_21;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_113, 0);
x_137 = lean_ctor_get(x_113, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_113);
x_138 = l_Lean_Meta_Simp_getSimprocExtension_x3f(x_108, x_137);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3;
x_11 = x_141;
x_12 = x_140;
goto block_21;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_143 = x_138;
} else {
 lean_dec_ref(x_138);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(3, 2, 0);
} else {
 x_144 = x_143;
 lean_ctor_set_tag(x_144, 3);
}
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_139);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_11 = x_146;
x_12 = x_142;
goto block_21;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_149 = x_138;
} else {
 lean_dec_ref(x_138);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(3, 2, 0);
} else {
 x_150 = x_149;
 lean_ctor_set_tag(x_150, 3);
}
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_147);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_11 = x_152;
x_12 = x_148;
goto block_21;
}
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_109);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_109, 1);
x_155 = lean_ctor_get(x_109, 0);
lean_dec(x_155);
x_156 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_156, 0, x_108);
x_157 = lean_box(0);
lean_ctor_set_tag(x_109, 1);
lean_ctor_set(x_109, 1, x_157);
lean_ctor_set(x_109, 0, x_156);
x_11 = x_109;
x_12 = x_154;
goto block_21;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_109, 1);
lean_inc(x_158);
lean_dec(x_109);
x_159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_159, 0, x_108);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_11 = x_161;
x_12 = x_158;
goto block_21;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; 
lean_dec(x_1);
x_162 = lean_ctor_get(x_104, 1);
lean_inc(x_162);
lean_dec(x_104);
x_163 = !lean_is_exclusive(x_105);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_105, 0);
lean_inc(x_164);
x_165 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(x_164, x_6, x_7, x_8, x_9, x_162);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_ctor_get(x_165, 0);
lean_dec(x_169);
x_170 = lean_box(0);
lean_ctor_set_tag(x_165, 1);
lean_ctor_set(x_165, 1, x_170);
lean_ctor_set(x_165, 0, x_105);
x_11 = x_165;
x_12 = x_168;
goto block_21;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_165, 1);
lean_inc(x_171);
lean_dec(x_165);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_105);
lean_ctor_set(x_173, 1, x_172);
x_11 = x_173;
x_12 = x_171;
goto block_21;
}
}
else
{
uint8_t x_174; 
lean_free_object(x_105);
lean_dec(x_164);
x_174 = !lean_is_exclusive(x_165);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_ctor_get(x_165, 1);
x_176 = lean_ctor_get(x_165, 0);
lean_dec(x_176);
x_177 = !lean_is_exclusive(x_166);
if (x_177 == 0)
{
lean_object* x_178; 
lean_ctor_set_tag(x_166, 2);
x_178 = lean_box(0);
lean_ctor_set_tag(x_165, 1);
lean_ctor_set(x_165, 1, x_178);
x_11 = x_165;
x_12 = x_175;
goto block_21;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_166, 0);
lean_inc(x_179);
lean_dec(x_166);
x_180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_box(0);
lean_ctor_set_tag(x_165, 1);
lean_ctor_set(x_165, 1, x_181);
lean_ctor_set(x_165, 0, x_180);
x_11 = x_165;
x_12 = x_175;
goto block_21;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_165, 1);
lean_inc(x_182);
lean_dec(x_165);
x_183 = lean_ctor_get(x_166, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_184 = x_166;
} else {
 lean_dec_ref(x_166);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(2, 1, 0);
} else {
 x_185 = x_184;
 lean_ctor_set_tag(x_185, 2);
}
lean_ctor_set(x_185, 0, x_183);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_11 = x_187;
x_12 = x_182;
goto block_21;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_105, 0);
lean_inc(x_188);
lean_dec(x_105);
lean_inc(x_188);
x_189 = l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(x_188, x_6, x_7, x_8, x_9, x_162);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_188);
x_194 = lean_box(0);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_192;
 lean_ctor_set_tag(x_195, 1);
}
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_11 = x_195;
x_12 = x_191;
goto block_21;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_188);
x_196 = lean_ctor_get(x_189, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_197 = x_189;
} else {
 lean_dec_ref(x_189);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_190, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_199 = x_190;
} else {
 lean_dec_ref(x_190);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(2, 1, 0);
} else {
 x_200 = x_199;
 lean_ctor_set_tag(x_200, 2);
}
lean_ctor_set(x_200, 0, x_198);
x_201 = lean_box(0);
if (lean_is_scalar(x_197)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_197;
 lean_ctor_set_tag(x_202, 1);
}
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_11 = x_202;
x_12 = x_196;
goto block_21;
}
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_104, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_104, 1);
lean_inc(x_204);
lean_dec(x_104);
x_50 = x_203;
x_51 = x_204;
goto block_101;
}
block_101:
{
uint8_t x_52; 
x_52 = l_Lean_Exception_isInterrupt(x_50);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Exception_isRuntime(x_50);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_50);
lean_dec(x_49);
x_54 = 0;
x_55 = l_Lean_Elab_Tactic_SavedState_restore(x_47, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_58 = lean_erase_macro_scopes(x_57);
x_59 = l_Lean_Meta_getSimpExtension_x3f(x_58, x_56);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = l_Lean_Meta_Simp_getSimprocExtension_x3f(x_58, x_62);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_free_object(x_59);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3;
x_11 = x_66;
x_12 = x_65;
goto block_21;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
x_69 = lean_ctor_get(x_63, 0);
lean_dec(x_69);
lean_ctor_set_tag(x_63, 3);
lean_ctor_set(x_63, 1, x_64);
lean_ctor_set(x_63, 0, x_61);
x_70 = lean_box(0);
lean_ctor_set(x_59, 1, x_70);
lean_ctor_set(x_59, 0, x_63);
x_11 = x_59;
x_12 = x_68;
goto block_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_dec(x_63);
x_72 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_64);
x_73 = lean_box(0);
lean_ctor_set(x_59, 1, x_73);
lean_ctor_set(x_59, 0, x_72);
x_11 = x_59;
x_12 = x_71;
goto block_21;
}
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_63);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_ctor_set_tag(x_63, 3);
lean_ctor_set(x_63, 1, x_75);
lean_ctor_set(x_63, 0, x_61);
x_77 = lean_box(0);
lean_ctor_set(x_59, 1, x_77);
lean_ctor_set(x_59, 0, x_63);
x_11 = x_59;
x_12 = x_76;
goto block_21;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_63);
x_80 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_80, 0, x_61);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_box(0);
lean_ctor_set(x_59, 1, x_81);
lean_ctor_set(x_59, 0, x_80);
x_11 = x_59;
x_12 = x_79;
goto block_21;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_59, 0);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_59);
x_84 = l_Lean_Meta_Simp_getSimprocExtension_x3f(x_58, x_83);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3;
x_11 = x_87;
x_12 = x_86;
goto block_21;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_89 = x_84;
} else {
 lean_dec_ref(x_84);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(3, 2, 0);
} else {
 x_90 = x_89;
 lean_ctor_set_tag(x_90, 3);
}
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_85);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_11 = x_92;
x_12 = x_88;
goto block_21;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_84, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_95 = x_84;
} else {
 lean_dec_ref(x_84);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(3, 2, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 3);
}
lean_ctor_set(x_96, 0, x_82);
lean_ctor_set(x_96, 1, x_93);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_11 = x_98;
x_12 = x_94;
goto block_21;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_49;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_50);
lean_ctor_set(x_99, 1, x_51);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_49;
 lean_ctor_set_tag(x_100, 1);
}
lean_ctor_set(x_100, 0, x_50);
lean_ctor_set(x_100, 1, x_51);
return x_100;
}
}
}
block_21:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
lean_ctor_set(x_11, 1, x_12);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 1, x_12);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_num___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
lean_inc(x_35);
lean_inc(x_34);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_35, x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_st_ref_take(x_1, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 7, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_50, 6, x_48);
x_51 = lean_st_ref_set(x_1, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg___boxed), 2, 0);
return x_8;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = 0;
x_12 = l_Lean_MessageData_ofConstName(x_1, x_11);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
static lean_object* _init_l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___closed__1;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
x_15 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
x_16 = 2;
x_17 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = l_Lean_Meta_Origin_key(x_1);
x_14 = l_Lean_MessageData_ofName(x_13);
x_15 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Origin_converse(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_16);
lean_inc(x_2);
x_17 = l_Lean_Meta_SimpTheorems_isLemma(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1(x_1, x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_1);
x_20 = l_Lean_Meta_SimpTheorems_eraseCore(x_2, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_12 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(x_2, x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_inc(x_1);
x_18 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
x_20 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_19, x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(x_2, x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
x_23 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_9);
x_25 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(x_2, x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(x_2, x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_31 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_11);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_box(0);
x_167 = l_Lean_Elab_Tactic_saveState___rarg(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_18);
x_170 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_18, x_19, x_14, x_15, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_168);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_171);
x_20 = x_173;
x_21 = x_172;
goto block_166;
}
else
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_170);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_ctor_get(x_170, 0);
x_176 = lean_ctor_get(x_170, 1);
x_177 = l_Lean_Exception_isInterrupt(x_175);
if (x_177 == 0)
{
uint8_t x_178; 
x_178 = l_Lean_Exception_isRuntime(x_175);
if (x_178 == 0)
{
uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_free_object(x_170);
x_179 = 0;
x_180 = l_Lean_Elab_Tactic_SavedState_restore(x_168, x_179, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_176);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_175);
x_20 = x_182;
x_21 = x_181;
goto block_166;
}
else
{
lean_dec(x_168);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_170;
}
}
else
{
lean_dec(x_168);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_170;
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_170, 0);
x_184 = lean_ctor_get(x_170, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_170);
x_185 = l_Lean_Exception_isInterrupt(x_183);
if (x_185 == 0)
{
uint8_t x_186; 
x_186 = l_Lean_Exception_isRuntime(x_183);
if (x_186 == 0)
{
uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = 0;
x_188 = l_Lean_Elab_Tactic_SavedState_restore(x_168, x_187, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_183);
x_20 = x_190;
x_21 = x_189;
goto block_166;
}
else
{
lean_object* x_191; 
lean_dec(x_168);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_183);
lean_ctor_set(x_191, 1, x_184);
return x_191;
}
}
else
{
lean_object* x_192; 
lean_dec(x_168);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_183);
lean_ctor_set(x_192, 1, x_184);
return x_192;
}
}
}
block_166:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_20);
x_22 = l_Lean_Syntax_getId(x_18);
x_23 = lean_erase_macro_scopes(x_22);
x_24 = l_Lean_Meta_Simp_isBuiltinSimproc(x_23, x_14, x_15, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_14, 5);
x_30 = l_Lean_replaceRef(x_18, x_29);
lean_dec(x_29);
lean_dec(x_18);
lean_ctor_set(x_14, 5, x_30);
x_31 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
lean_dec(x_15);
lean_dec(x_14);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
x_38 = lean_ctor_get(x_14, 2);
x_39 = lean_ctor_get(x_14, 3);
x_40 = lean_ctor_get(x_14, 4);
x_41 = lean_ctor_get(x_14, 5);
x_42 = lean_ctor_get(x_14, 6);
x_43 = lean_ctor_get(x_14, 7);
x_44 = lean_ctor_get(x_14, 8);
x_45 = lean_ctor_get(x_14, 9);
x_46 = lean_ctor_get(x_14, 10);
x_47 = lean_ctor_get_uint8(x_14, sizeof(void*)*12);
x_48 = lean_ctor_get(x_14, 11);
x_49 = lean_ctor_get_uint8(x_14, sizeof(void*)*12 + 1);
lean_inc(x_48);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_50 = l_Lean_replaceRef(x_18, x_41);
lean_dec(x_41);
lean_dec(x_18);
x_51 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_37);
lean_ctor_set(x_51, 2, x_38);
lean_ctor_set(x_51, 3, x_39);
lean_ctor_set(x_51, 4, x_40);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_51, 6, x_42);
lean_ctor_set(x_51, 7, x_43);
lean_ctor_set(x_51, 8, x_44);
lean_ctor_set(x_51, 9, x_45);
lean_ctor_set(x_51, 10, x_46);
lean_ctor_set(x_51, 11, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*12, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*12 + 1, x_49);
x_52 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_51, x_15, x_27);
lean_dec(x_15);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_57 = !lean_is_exclusive(x_24);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_24, 0);
lean_dec(x_58);
x_59 = l_Lean_Meta_Simp_SimprocsArray_erase(x_5, x_23);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_3);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_24, 0, x_64);
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_dec(x_24);
x_66 = l_Lean_Meta_Simp_SimprocsArray_erase(x_5, x_23);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_2);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_20, 0);
lean_inc(x_73);
lean_dec(x_20);
lean_inc(x_73);
x_74 = l_Lean_Meta_Simp_isSimproc(x_73, x_14, x_15, x_21);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_4, 0);
x_78 = lean_ctor_get_uint8(x_77, sizeof(void*)*2 + 11);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec(x_74);
x_80 = 1;
x_81 = 0;
x_82 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 1, x_81);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_14, 5);
x_85 = l_Lean_replaceRef(x_18, x_84);
lean_dec(x_84);
lean_dec(x_18);
lean_ctor_set(x_14, 5, x_85);
x_86 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4(x_6, x_82, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_79);
lean_dec(x_15);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_2);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_3);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_86, 0, x_93);
return x_86;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_86, 0);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_86);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_2);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_3);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_5);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_95);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_102 = lean_ctor_get(x_14, 0);
x_103 = lean_ctor_get(x_14, 1);
x_104 = lean_ctor_get(x_14, 2);
x_105 = lean_ctor_get(x_14, 3);
x_106 = lean_ctor_get(x_14, 4);
x_107 = lean_ctor_get(x_14, 5);
x_108 = lean_ctor_get(x_14, 6);
x_109 = lean_ctor_get(x_14, 7);
x_110 = lean_ctor_get(x_14, 8);
x_111 = lean_ctor_get(x_14, 9);
x_112 = lean_ctor_get(x_14, 10);
x_113 = lean_ctor_get_uint8(x_14, sizeof(void*)*12);
x_114 = lean_ctor_get(x_14, 11);
x_115 = lean_ctor_get_uint8(x_14, sizeof(void*)*12 + 1);
lean_inc(x_114);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_14);
x_116 = l_Lean_replaceRef(x_18, x_107);
lean_dec(x_107);
lean_dec(x_18);
x_117 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_103);
lean_ctor_set(x_117, 2, x_104);
lean_ctor_set(x_117, 3, x_105);
lean_ctor_set(x_117, 4, x_106);
lean_ctor_set(x_117, 5, x_116);
lean_ctor_set(x_117, 6, x_108);
lean_ctor_set(x_117, 7, x_109);
lean_ctor_set(x_117, 8, x_110);
lean_ctor_set(x_117, 9, x_111);
lean_ctor_set(x_117, 10, x_112);
lean_ctor_set(x_117, 11, x_114);
lean_ctor_set_uint8(x_117, sizeof(void*)*12, x_113);
lean_ctor_set_uint8(x_117, sizeof(void*)*12 + 1, x_115);
x_118 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4(x_6, x_82, x_8, x_9, x_10, x_11, x_12, x_13, x_117, x_15, x_79);
lean_dec(x_15);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_2);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_3);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_5);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
if (lean_is_scalar(x_121)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_121;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_120);
return x_127;
}
}
else
{
uint8_t x_128; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_128 = !lean_is_exclusive(x_74);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_129 = lean_ctor_get(x_74, 0);
lean_dec(x_129);
x_130 = 1;
x_131 = 0;
x_132 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_132, 0, x_73);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1 + 1, x_131);
x_133 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_2);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_3);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_5);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_74, 0, x_138);
return x_74;
}
else
{
lean_object* x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_139 = lean_ctor_get(x_74, 1);
lean_inc(x_139);
lean_dec(x_74);
x_140 = 1;
x_141 = 0;
x_142 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_142, 0, x_73);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1 + 1, x_141);
x_143 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_2);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_3);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_5);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_139);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_150 = !lean_is_exclusive(x_74);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_74, 0);
lean_dec(x_151);
x_152 = l_Lean_Meta_Simp_SimprocsArray_erase(x_5, x_73);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_6);
lean_ctor_set(x_153, 1, x_2);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_3);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_74, 0, x_157);
return x_74;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_74, 1);
lean_inc(x_158);
lean_dec(x_74);
x_159 = l_Lean_Meta_Simp_SimprocsArray_erase(x_5, x_73);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_6);
lean_ctor_set(x_160, 1, x_2);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_3);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_158);
return x_165;
}
}
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_15);
lean_dec(x_14);
x_193 = !lean_is_exclusive(x_7);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = lean_ctor_get(x_7, 0);
x_195 = l_Lean_Expr_fvarId_x21(x_194);
lean_dec(x_194);
lean_ctor_set(x_7, 0, x_195);
x_196 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_7);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_2);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_3);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_5);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_16);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_203 = lean_ctor_get(x_7, 0);
lean_inc(x_203);
lean_dec(x_7);
x_204 = l_Lean_Expr_fvarId_x21(x_203);
lean_dec(x_203);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_2);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_3);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_5);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_box(0);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_16);
return x_212;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpErase", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpLemma", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpStar", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpPost", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_38; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_511; 
x_19 = lean_array_uget(x_4, x_6);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_93 = x_7;
} else {
 lean_dec_ref(x_7);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
lean_inc(x_19);
x_99 = l_Lean_Syntax_getKind(x_19);
x_100 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2;
x_101 = lean_name_eq(x_99, x_100);
x_511 = l_Lean_Elab_Tactic_saveState___rarg(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (x_101 == 0)
{
lean_object* x_512; lean_object* x_513; uint8_t x_514; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = 0;
x_102 = x_514;
x_103 = x_512;
x_104 = x_513;
goto block_510;
}
else
{
lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_515 = lean_ctor_get(x_511, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_511, 1);
lean_inc(x_516);
lean_dec(x_511);
x_517 = 1;
x_102 = x_517;
x_103 = x_515;
x_104 = x_516;
goto block_510;
}
block_37:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = 1;
x_31 = lean_usize_add(x_6, x_30);
x_6 = x_31;
x_7 = x_29;
x_16 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
block_89:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_40, 1);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_41, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_38, 0, x_50);
x_20 = x_38;
goto block_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_41, 1, x_53);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_38, 0, x_54);
x_20 = x_38;
goto block_37;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
lean_dec(x_41);
x_56 = lean_ctor_get(x_42, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_58 = x_42;
} else {
 lean_dec_ref(x_42);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_40, 1, x_60);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_40);
lean_ctor_set(x_38, 0, x_61);
x_20 = x_38;
goto block_37;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
lean_dec(x_40);
x_63 = lean_ctor_get(x_41, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_64 = x_41;
} else {
 lean_dec_ref(x_41);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_67 = x_42;
} else {
 lean_dec_ref(x_42);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_38, 0, x_71);
x_20 = x_38;
goto block_37;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_72 = lean_ctor_get(x_38, 1);
lean_inc(x_72);
lean_dec(x_38);
x_73 = lean_ctor_get(x_40, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_74 = x_40;
} else {
 lean_dec_ref(x_40);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_41, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_42, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_79 = x_42;
} else {
 lean_dec_ref(x_42);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_74)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_74;
}
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_72);
x_20 = x_84;
goto block_37;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_38);
if (x_85 == 0)
{
x_20 = x_38;
goto block_37;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_38, 0);
x_87 = lean_ctor_get(x_38, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_38);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_20 = x_88;
goto block_37;
}
}
}
block_510:
{
lean_object* x_105; lean_object* x_106; 
if (x_102 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_139 = lean_name_eq(x_99, x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
lean_dec(x_19);
x_140 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
x_141 = lean_name_eq(x_99, x_140);
lean_dec(x_99);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg(x_104);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_105 = x_143;
x_106 = x_144;
goto block_137;
}
else
{
lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_96);
lean_ctor_set(x_145, 1, x_97);
x_146 = 1;
x_147 = lean_box(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_92);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_104);
x_38 = x_152;
goto block_89;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_99);
x_153 = lean_unsigned_to_nat(0u);
x_154 = l_Lean_Syntax_getArg(x_19, x_153);
x_155 = l_Lean_Syntax_isNone(x_154);
x_156 = lean_unsigned_to_nat(1u);
x_157 = l_Lean_Syntax_getArg(x_19, x_156);
x_158 = l_Lean_Syntax_isNone(x_157);
lean_dec(x_157);
x_159 = lean_unsigned_to_nat(2u);
x_160 = l_Lean_Syntax_getArg(x_19, x_159);
if (x_155 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_484 = l_Lean_Syntax_getArg(x_154, x_153);
lean_dec(x_154);
x_485 = l_Lean_Syntax_getKind(x_484);
x_486 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8;
x_487 = lean_name_eq(x_485, x_486);
lean_dec(x_485);
x_161 = x_487;
goto block_483;
}
else
{
uint8_t x_488; 
lean_dec(x_154);
x_488 = 1;
x_161 = x_488;
goto block_483;
}
block_483:
{
uint8_t x_162; 
if (x_158 == 0)
{
uint8_t x_481; 
x_481 = 1;
x_162 = x_481;
goto block_480;
}
else
{
uint8_t x_482; 
x_482 = 0;
x_162 = x_482;
goto block_480;
}
block_480:
{
lean_object* x_163; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_160);
x_163 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(x_160, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_104);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
switch (lean_obj_tag(x_164)) {
case 0:
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_163);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_163, 1);
x_167 = lean_ctor_get(x_163, 0);
lean_dec(x_167);
x_168 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_15, x_166);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_168, 1);
lean_ctor_set_tag(x_168, 2);
lean_ctor_set(x_168, 1, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_96);
x_171 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_96, x_168, x_160, x_161, x_162, x_10, x_11, x_12, x_13, x_14, x_15, x_170);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_171, 0);
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_173);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_94);
lean_ctor_set(x_174, 1, x_163);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_92);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_171, 0, x_177);
x_38 = x_171;
goto block_89;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_ctor_get(x_171, 0);
x_179 = lean_ctor_get(x_171, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_171);
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_94);
lean_ctor_set(x_180, 1, x_163);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_92);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_box(0);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_179);
x_38 = x_184;
goto block_89;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_free_object(x_163);
x_185 = lean_ctor_get(x_171, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_171, 1);
lean_inc(x_186);
lean_dec(x_171);
x_105 = x_185;
x_106 = x_186;
goto block_137;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_168, 0);
x_188 = lean_ctor_get(x_168, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_168);
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_96);
x_190 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_96, x_189, x_160, x_161, x_162, x_10, x_11, x_12, x_13, x_14, x_15, x_188);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_191);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_94);
lean_ctor_set(x_194, 1, x_163);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_92);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_193;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_192);
x_38 = x_198;
goto block_89;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_free_object(x_163);
x_199 = lean_ctor_get(x_190, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_190, 1);
lean_inc(x_200);
lean_dec(x_190);
x_105 = x_199;
x_106 = x_200;
goto block_137;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_163, 1);
lean_inc(x_201);
lean_dec(x_163);
x_202 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_15, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(2, 2, 0);
} else {
 x_206 = x_205;
 lean_ctor_set_tag(x_206, 2);
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_96);
x_207 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_96, x_206, x_160, x_161, x_162, x_10, x_11, x_12, x_13, x_14, x_15, x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_97);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_94);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_92);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_box(0);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
if (lean_is_scalar(x_210)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_210;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_209);
x_38 = x_216;
goto block_89;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_207, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_207, 1);
lean_inc(x_218);
lean_dec(x_207);
x_105 = x_217;
x_106 = x_218;
goto block_137;
}
}
}
case 1:
{
uint8_t x_219; 
lean_dec(x_160);
x_219 = !lean_is_exclusive(x_163);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_220 = lean_ctor_get(x_163, 1);
x_221 = lean_ctor_get(x_163, 0);
lean_dec(x_221);
x_222 = lean_ctor_get(x_164, 0);
lean_inc(x_222);
lean_dec(x_164);
x_223 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_15, x_220);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_223, 1);
lean_ctor_set_tag(x_223, 2);
lean_ctor_set(x_223, 1, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_96);
x_226 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_96, x_223, x_222, x_161, x_162, x_3, x_12, x_13, x_14, x_15, x_225);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_228 = lean_ctor_get(x_226, 0);
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_228);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_94);
lean_ctor_set(x_229, 1, x_163);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_92);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_box(0);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
lean_ctor_set(x_226, 0, x_232);
x_38 = x_226;
goto block_89;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_ctor_get(x_226, 0);
x_234 = lean_ctor_get(x_226, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_226);
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_94);
lean_ctor_set(x_235, 1, x_163);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_92);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_234);
x_38 = x_239;
goto block_89;
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_free_object(x_163);
x_240 = lean_ctor_get(x_226, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_226, 1);
lean_inc(x_241);
lean_dec(x_226);
x_105 = x_240;
x_106 = x_241;
goto block_137;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_223, 0);
x_243 = lean_ctor_get(x_223, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_223);
x_244 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_96);
x_245 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_96, x_244, x_222, x_161, x_162, x_3, x_12, x_13, x_14, x_15, x_243);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_248 = x_245;
} else {
 lean_dec_ref(x_245);
 x_248 = lean_box(0);
}
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_246);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_94);
lean_ctor_set(x_249, 1, x_163);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_92);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
if (lean_is_scalar(x_248)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_248;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_247);
x_38 = x_253;
goto block_89;
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_free_object(x_163);
x_254 = lean_ctor_get(x_245, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_245, 1);
lean_inc(x_255);
lean_dec(x_245);
x_105 = x_254;
x_106 = x_255;
goto block_137;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_256 = lean_ctor_get(x_163, 1);
lean_inc(x_256);
lean_dec(x_163);
x_257 = lean_ctor_get(x_164, 0);
lean_inc(x_257);
lean_dec(x_164);
x_258 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_15, x_256);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_261 = x_258;
} else {
 lean_dec_ref(x_258);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(2, 2, 0);
} else {
 x_262 = x_261;
 lean_ctor_set_tag(x_262, 2);
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_96);
x_263 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_96, x_262, x_257, x_161, x_162, x_3, x_12, x_13, x_14, x_15, x_260);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_97);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_94);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_92);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
if (lean_is_scalar(x_266)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_266;
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_265);
x_38 = x_272;
goto block_89;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_263, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_263, 1);
lean_inc(x_274);
lean_dec(x_263);
x_105 = x_273;
x_106 = x_274;
goto block_137;
}
}
}
case 2:
{
uint8_t x_275; 
lean_dec(x_160);
lean_dec(x_19);
x_275 = !lean_is_exclusive(x_163);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_163, 1);
x_277 = lean_ctor_get(x_163, 0);
lean_dec(x_277);
x_278 = lean_ctor_get(x_164, 0);
lean_inc(x_278);
lean_dec(x_164);
lean_inc(x_92);
x_279 = l_Lean_Meta_Simp_SimprocsArray_add(x_92, x_278, x_161, x_14, x_15, x_276);
if (lean_obj_tag(x_279) == 0)
{
uint8_t x_280; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_92);
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_279, 0);
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_96);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_94);
lean_ctor_set(x_282, 1, x_163);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_box(0);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
lean_ctor_set(x_279, 0, x_285);
x_38 = x_279;
goto block_89;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_279, 0);
x_287 = lean_ctor_get(x_279, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_279);
lean_ctor_set(x_163, 1, x_97);
lean_ctor_set(x_163, 0, x_96);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_94);
lean_ctor_set(x_288, 1, x_163);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_288);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_287);
x_38 = x_292;
goto block_89;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_free_object(x_163);
x_293 = lean_ctor_get(x_279, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_279, 1);
lean_inc(x_294);
lean_dec(x_279);
x_105 = x_293;
x_106 = x_294;
goto block_137;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_163, 1);
lean_inc(x_295);
lean_dec(x_163);
x_296 = lean_ctor_get(x_164, 0);
lean_inc(x_296);
lean_dec(x_164);
lean_inc(x_92);
x_297 = l_Lean_Meta_Simp_SimprocsArray_add(x_92, x_296, x_161, x_14, x_15, x_295);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_92);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_96);
lean_ctor_set(x_301, 1, x_97);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_94);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_298);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_303);
if (lean_is_scalar(x_300)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_300;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_299);
x_38 = x_306;
goto block_89;
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_297, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_297, 1);
lean_inc(x_308);
lean_dec(x_297);
x_105 = x_307;
x_106 = x_308;
goto block_137;
}
}
}
default: 
{
lean_object* x_309; 
lean_dec(x_160);
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_19);
x_309 = lean_ctor_get(x_164, 0);
lean_inc(x_309);
if (lean_obj_tag(x_309) == 0)
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_164);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_311 = lean_ctor_get(x_164, 1);
x_312 = lean_ctor_get(x_164, 0);
lean_dec(x_312);
x_313 = !lean_is_exclusive(x_163);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_314 = lean_ctor_get(x_163, 1);
x_315 = lean_ctor_get(x_163, 0);
lean_dec(x_315);
x_316 = lean_ctor_get(x_311, 0);
lean_inc(x_316);
lean_dec(x_311);
x_317 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_316, x_14, x_15, x_314);
lean_dec(x_316);
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_317, 0);
x_320 = lean_array_push(x_92, x_319);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_97);
lean_ctor_set(x_164, 0, x_96);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_163, 0, x_94);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_163);
x_322 = lean_box(0);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_321);
lean_ctor_set(x_317, 0, x_323);
x_38 = x_317;
goto block_89;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_324 = lean_ctor_get(x_317, 0);
x_325 = lean_ctor_get(x_317, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_317);
x_326 = lean_array_push(x_92, x_324);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_97);
lean_ctor_set(x_164, 0, x_96);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_163, 0, x_94);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_163);
x_328 = lean_box(0);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_325);
x_38 = x_330;
goto block_89;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_331 = lean_ctor_get(x_163, 1);
lean_inc(x_331);
lean_dec(x_163);
x_332 = lean_ctor_get(x_311, 0);
lean_inc(x_332);
lean_dec(x_311);
x_333 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_332, x_14, x_15, x_331);
lean_dec(x_332);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
x_337 = lean_array_push(x_92, x_334);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_97);
lean_ctor_set(x_164, 0, x_96);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_94);
lean_ctor_set(x_338, 1, x_164);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_box(0);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
if (lean_is_scalar(x_336)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_336;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_335);
x_38 = x_342;
goto block_89;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_343 = lean_ctor_get(x_164, 1);
lean_inc(x_343);
lean_dec(x_164);
x_344 = lean_ctor_get(x_163, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_345 = x_163;
} else {
 lean_dec_ref(x_163);
 x_345 = lean_box(0);
}
x_346 = lean_ctor_get(x_343, 0);
lean_inc(x_346);
lean_dec(x_343);
x_347 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_346, x_14, x_15, x_344);
lean_dec(x_346);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_350 = x_347;
} else {
 lean_dec_ref(x_347);
 x_350 = lean_box(0);
}
x_351 = lean_array_push(x_92, x_348);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_96);
lean_ctor_set(x_352, 1, x_97);
if (lean_is_scalar(x_345)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_345;
}
lean_ctor_set(x_353, 0, x_94);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_box(0);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
if (lean_is_scalar(x_350)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_350;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_349);
x_38 = x_357;
goto block_89;
}
}
else
{
uint8_t x_358; 
x_358 = !lean_is_exclusive(x_164);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_164, 1);
x_360 = lean_ctor_get(x_164, 0);
lean_dec(x_360);
if (lean_obj_tag(x_359) == 0)
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_163);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_362 = lean_ctor_get(x_163, 1);
x_363 = lean_ctor_get(x_163, 0);
lean_dec(x_363);
x_364 = lean_ctor_get(x_309, 0);
lean_inc(x_364);
lean_dec(x_309);
x_365 = l_Lean_Meta_SimpExtension_getTheorems(x_364, x_14, x_15, x_362);
lean_dec(x_364);
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_367 = lean_ctor_get(x_365, 0);
x_368 = lean_array_push(x_97, x_367);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_368);
lean_ctor_set(x_164, 0, x_96);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_163, 0, x_94);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_92);
lean_ctor_set(x_369, 1, x_163);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
lean_ctor_set(x_365, 0, x_371);
x_38 = x_365;
goto block_89;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_372 = lean_ctor_get(x_365, 0);
x_373 = lean_ctor_get(x_365, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_365);
x_374 = lean_array_push(x_97, x_372);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_374);
lean_ctor_set(x_164, 0, x_96);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_163, 0, x_94);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_92);
lean_ctor_set(x_375, 1, x_163);
x_376 = lean_box(0);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_373);
x_38 = x_378;
goto block_89;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_379 = lean_ctor_get(x_163, 1);
lean_inc(x_379);
lean_dec(x_163);
x_380 = lean_ctor_get(x_309, 0);
lean_inc(x_380);
lean_dec(x_309);
x_381 = l_Lean_Meta_SimpExtension_getTheorems(x_380, x_14, x_15, x_379);
lean_dec(x_380);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_384 = x_381;
} else {
 lean_dec_ref(x_381);
 x_384 = lean_box(0);
}
x_385 = lean_array_push(x_97, x_382);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_385);
lean_ctor_set(x_164, 0, x_96);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_94);
lean_ctor_set(x_386, 1, x_164);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_92);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_box(0);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_387);
if (lean_is_scalar(x_384)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_384;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_383);
x_38 = x_390;
goto block_89;
}
}
else
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_163);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_392 = lean_ctor_get(x_163, 1);
x_393 = lean_ctor_get(x_163, 0);
lean_dec(x_393);
x_394 = lean_ctor_get(x_309, 0);
lean_inc(x_394);
lean_dec(x_309);
x_395 = lean_ctor_get(x_359, 0);
lean_inc(x_395);
lean_dec(x_359);
x_396 = l_Lean_Meta_SimpExtension_getTheorems(x_394, x_14, x_15, x_392);
lean_dec(x_394);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_398 = lean_ctor_get(x_396, 0);
x_399 = lean_ctor_get(x_396, 1);
x_400 = lean_array_push(x_97, x_398);
x_401 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_395, x_14, x_15, x_399);
lean_dec(x_395);
x_402 = !lean_is_exclusive(x_401);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_401, 0);
x_404 = lean_array_push(x_92, x_403);
lean_ctor_set(x_396, 1, x_400);
lean_ctor_set(x_396, 0, x_96);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_396);
lean_ctor_set(x_164, 0, x_94);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_163, 0, x_404);
x_405 = lean_box(0);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_163);
lean_ctor_set(x_401, 0, x_406);
x_38 = x_401;
goto block_89;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_407 = lean_ctor_get(x_401, 0);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_401);
x_409 = lean_array_push(x_92, x_407);
lean_ctor_set(x_396, 1, x_400);
lean_ctor_set(x_396, 0, x_96);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_396);
lean_ctor_set(x_164, 0, x_94);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_163, 0, x_409);
x_410 = lean_box(0);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_163);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_408);
x_38 = x_412;
goto block_89;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_413 = lean_ctor_get(x_396, 0);
x_414 = lean_ctor_get(x_396, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_396);
x_415 = lean_array_push(x_97, x_413);
x_416 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_395, x_14, x_15, x_414);
lean_dec(x_395);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_419 = x_416;
} else {
 lean_dec_ref(x_416);
 x_419 = lean_box(0);
}
x_420 = lean_array_push(x_92, x_417);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_96);
lean_ctor_set(x_421, 1, x_415);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_421);
lean_ctor_set(x_164, 0, x_94);
lean_ctor_set(x_163, 1, x_164);
lean_ctor_set(x_163, 0, x_420);
x_422 = lean_box(0);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_163);
if (lean_is_scalar(x_419)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_419;
}
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_418);
x_38 = x_424;
goto block_89;
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_425 = lean_ctor_get(x_163, 1);
lean_inc(x_425);
lean_dec(x_163);
x_426 = lean_ctor_get(x_309, 0);
lean_inc(x_426);
lean_dec(x_309);
x_427 = lean_ctor_get(x_359, 0);
lean_inc(x_427);
lean_dec(x_359);
x_428 = l_Lean_Meta_SimpExtension_getTheorems(x_426, x_14, x_15, x_425);
lean_dec(x_426);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_431 = x_428;
} else {
 lean_dec_ref(x_428);
 x_431 = lean_box(0);
}
x_432 = lean_array_push(x_97, x_429);
x_433 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_427, x_14, x_15, x_430);
lean_dec(x_427);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_436 = x_433;
} else {
 lean_dec_ref(x_433);
 x_436 = lean_box(0);
}
x_437 = lean_array_push(x_92, x_434);
if (lean_is_scalar(x_431)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_431;
}
lean_ctor_set(x_438, 0, x_96);
lean_ctor_set(x_438, 1, x_432);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 1, x_438);
lean_ctor_set(x_164, 0, x_94);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_164);
x_440 = lean_box(0);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_439);
if (lean_is_scalar(x_436)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_436;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_435);
x_38 = x_442;
goto block_89;
}
}
}
else
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_164, 1);
lean_inc(x_443);
lean_dec(x_164);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_444 = lean_ctor_get(x_163, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_445 = x_163;
} else {
 lean_dec_ref(x_163);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_309, 0);
lean_inc(x_446);
lean_dec(x_309);
x_447 = l_Lean_Meta_SimpExtension_getTheorems(x_446, x_14, x_15, x_444);
lean_dec(x_446);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_450 = x_447;
} else {
 lean_dec_ref(x_447);
 x_450 = lean_box(0);
}
x_451 = lean_array_push(x_97, x_448);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_96);
lean_ctor_set(x_452, 1, x_451);
if (lean_is_scalar(x_445)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_445;
}
lean_ctor_set(x_453, 0, x_94);
lean_ctor_set(x_453, 1, x_452);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_92);
lean_ctor_set(x_454, 1, x_453);
x_455 = lean_box(0);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
if (lean_is_scalar(x_450)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_450;
}
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_449);
x_38 = x_457;
goto block_89;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_458 = lean_ctor_get(x_163, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_459 = x_163;
} else {
 lean_dec_ref(x_163);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_309, 0);
lean_inc(x_460);
lean_dec(x_309);
x_461 = lean_ctor_get(x_443, 0);
lean_inc(x_461);
lean_dec(x_443);
x_462 = l_Lean_Meta_SimpExtension_getTheorems(x_460, x_14, x_15, x_458);
lean_dec(x_460);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_465 = x_462;
} else {
 lean_dec_ref(x_462);
 x_465 = lean_box(0);
}
x_466 = lean_array_push(x_97, x_463);
x_467 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_461, x_14, x_15, x_464);
lean_dec(x_461);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_470 = x_467;
} else {
 lean_dec_ref(x_467);
 x_470 = lean_box(0);
}
x_471 = lean_array_push(x_92, x_468);
if (lean_is_scalar(x_465)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_465;
}
lean_ctor_set(x_472, 0, x_96);
lean_ctor_set(x_472, 1, x_466);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_94);
lean_ctor_set(x_473, 1, x_472);
if (lean_is_scalar(x_459)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_459;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_box(0);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_474);
if (lean_is_scalar(x_470)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_470;
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_469);
x_38 = x_477;
goto block_89;
}
}
}
}
}
}
else
{
lean_object* x_478; lean_object* x_479; 
lean_dec(x_160);
lean_dec(x_19);
x_478 = lean_ctor_get(x_163, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_163, 1);
lean_inc(x_479);
lean_dec(x_163);
x_105 = x_478;
x_106 = x_479;
goto block_137;
}
}
}
}
}
else
{
lean_dec(x_99);
if (x_2 == 0)
{
uint8_t x_489; 
x_489 = lean_unbox(x_94);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_94);
lean_inc(x_97);
x_491 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_19, x_97, x_94, x_1, x_92, x_96, x_490, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_104);
lean_dec(x_19);
if (lean_obj_tag(x_491) == 0)
{
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_38 = x_491;
goto block_89;
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
x_105 = x_492;
x_106 = x_493;
goto block_137;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_494 = lean_unsigned_to_nat(1u);
x_495 = l_Lean_Syntax_getArg(x_19, x_494);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_10);
x_496 = l_Lean_Elab_Term_isLocalIdent_x3f(x_495, x_10, x_11, x_12, x_13, x_14, x_15, x_104);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_94);
lean_inc(x_97);
x_499 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_19, x_97, x_94, x_1, x_92, x_96, x_497, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_498);
lean_dec(x_19);
if (lean_obj_tag(x_499) == 0)
{
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_38 = x_499;
goto block_89;
}
else
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_105 = x_500;
x_106 = x_501;
goto block_137;
}
}
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_502 = lean_unsigned_to_nat(1u);
x_503 = l_Lean_Syntax_getArg(x_19, x_502);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_10);
x_504 = l_Lean_Elab_Term_isLocalIdent_x3f(x_503, x_10, x_11, x_12, x_13, x_14, x_15, x_104);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_94);
lean_inc(x_97);
x_507 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_19, x_97, x_94, x_1, x_92, x_96, x_505, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_506);
lean_dec(x_19);
if (lean_obj_tag(x_507) == 0)
{
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_38 = x_507;
goto block_89;
}
else
{
lean_object* x_508; lean_object* x_509; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_105 = x_508;
x_106 = x_509;
goto block_137;
}
}
}
block_137:
{
uint8_t x_107; 
x_107 = l_Lean_Exception_isInterrupt(x_105);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = l_Lean_Exception_isRuntime(x_105);
if (x_108 == 0)
{
uint8_t x_109; lean_object* x_110; uint8_t x_111; 
x_109 = 0;
x_110 = l_Lean_Elab_Tactic_SavedState_restore(x_103, x_109, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_106);
x_111 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
if (x_111 == 0)
{
uint8_t x_112; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set_tag(x_110, 1);
lean_ctor_set(x_110, 0, x_105);
x_38 = x_110;
goto block_89;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_114);
x_38 = x_115;
goto block_89;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
lean_dec(x_110);
lean_inc(x_14);
x_117 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_105, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_117, 0);
if (lean_is_scalar(x_98)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_98;
}
lean_ctor_set(x_120, 0, x_96);
lean_ctor_set(x_120, 1, x_97);
if (lean_is_scalar(x_95)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_95;
}
lean_ctor_set(x_121, 0, x_94);
lean_ctor_set(x_121, 1, x_120);
if (lean_is_scalar(x_93)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_93;
}
lean_ctor_set(x_122, 0, x_92);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_117, 0, x_123);
x_38 = x_117;
goto block_89;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_117, 0);
x_125 = lean_ctor_get(x_117, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_117);
if (lean_is_scalar(x_98)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_98;
}
lean_ctor_set(x_126, 0, x_96);
lean_ctor_set(x_126, 1, x_97);
if (lean_is_scalar(x_95)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_95;
}
lean_ctor_set(x_127, 0, x_94);
lean_ctor_set(x_127, 1, x_126);
if (lean_is_scalar(x_93)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_93;
}
lean_ctor_set(x_128, 0, x_92);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_38 = x_130;
goto block_89;
}
}
else
{
uint8_t x_131; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_131 = !lean_is_exclusive(x_117);
if (x_131 == 0)
{
x_38 = x_117;
goto block_89;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_117, 0);
x_133 = lean_ctor_get(x_117, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_117);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_38 = x_134;
goto block_89;
}
}
}
}
else
{
lean_object* x_135; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_105);
lean_ctor_set(x_135, 1, x_106);
x_38 = x_135;
goto block_89;
}
}
else
{
lean_object* x_136; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_105);
lean_ctor_set(x_136, 1, x_106);
x_38 = x_136;
goto block_89;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_elabSimpArgs___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get_uint32(x_1, sizeof(void*)*5);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_set(x_26, x_29, x_25);
x_31 = lean_ctor_get(x_1, 2);
x_32 = lean_ctor_get(x_1, 3);
x_33 = lean_ctor_get_uint32(x_1, sizeof(void*)*5 + 4);
x_34 = lean_ctor_get(x_1, 4);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 8);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_27);
x_36 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_34);
lean_ctor_set_uint32(x_36, sizeof(void*)*5, x_28);
lean_ctor_set_uint32(x_36, sizeof(void*)*5 + 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*5 + 8, x_35);
x_37 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
x_38 = lean_unbox(x_24);
lean_dec(x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_38);
lean_ctor_set(x_17, 0, x_37);
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_dec(x_17);
x_40 = lean_ctor_get(x_18, 0);
lean_inc(x_40);
lean_dec(x_18);
x_41 = lean_ctor_get(x_19, 0);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get_uint32(x_1, sizeof(void*)*5);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_set(x_43, x_46, x_42);
x_48 = lean_ctor_get(x_1, 2);
x_49 = lean_ctor_get(x_1, 3);
x_50 = lean_ctor_get_uint32(x_1, sizeof(void*)*5 + 4);
x_51 = lean_ctor_get(x_1, 4);
x_52 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 8);
lean_inc(x_51);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_44);
x_53 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set_uint32(x_53, sizeof(void*)*5, x_45);
lean_ctor_set_uint32(x_53, sizeof(void*)*5 + 4, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*5 + 8, x_52);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
x_55 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_39);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
return x_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Syntax_isNone(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; uint8_t x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_getSepArgs(x_21);
lean_dec(x_21);
x_23 = lean_array_size(x_22);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_Meta_instInhabitedSimpTheorems;
x_41 = l_outOfBounds___rarg(x_40);
x_25 = x_41;
goto block_39;
}
else
{
lean_object* x_42; 
x_42 = lean_array_fget(x_16, x_18);
x_25 = x_42;
goto block_39;
}
block_39:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_box(x_4);
x_32 = lean_box(x_5);
x_33 = lean_box_usize(x_23);
x_34 = l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1;
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabSimpArgs___lambda__1___boxed), 16, 7);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_31);
lean_closure_set(x_35, 2, x_32);
lean_closure_set(x_35, 3, x_22);
lean_closure_set(x_35, 4, x_33);
lean_closure_set(x_35, 5, x_34);
lean_closure_set(x_35, 6, x_30);
if (x_24 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_elabSimpArgs___spec__7(x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Elab_Tactic_withMainContext___rarg(x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_38;
}
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = 0;
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_14);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(x_1, x_17, x_18, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = l_Lean_Elab_Tactic_elabSimpArgs___lambda__1(x_1, x_17, x_18, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Lean_Elab_Tactic_elabSimpArgs(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_self", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("iff_self", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2;
x_2 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpOnlyBuiltins() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_array_uget(x_1, x_3);
lean_inc(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_17);
x_18 = l_Lean_Meta_SimpTheoremsArray_isErased(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_inc(x_9);
x_19 = l_Lean_FVarId_getDecl(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_toExpr(x_20);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_4, x_17, x_22, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_4 = x_24;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
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
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
size_t x_37; size_t x_38; 
lean_dec(x_17);
lean_dec(x_16);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = 1;
x_16 = 0;
x_17 = lean_unsigned_to_nat(1000u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_13, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_1 = x_19;
x_2 = x_14;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_15, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_23 = l_Lean_Elab_Tactic_elabSimpConfig(x_22, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
x_29 = l_UInt32_ofNatTruncate(x_28);
x_30 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_30);
lean_ctor_set(x_17, 0, x_3);
x_31 = lean_array_mk(x_17);
x_32 = lean_box(0);
x_33 = 0;
x_34 = lean_unsigned_to_nat(0u);
x_35 = 0;
x_36 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_19);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_34);
lean_ctor_set_uint32(x_36, sizeof(void*)*5, x_29);
lean_ctor_set_uint32(x_36, sizeof(void*)*5 + 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*5 + 8, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_30);
x_38 = lean_array_mk(x_37);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l_Lean_Elab_Tactic_elabSimpArgs(x_27, x_36, x_38, x_4, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
lean_dec(x_27);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*2);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_5);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
if (x_6 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_dec(x_39);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_dec(x_40);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
x_58 = lean_ctor_get(x_52, 2);
x_59 = lean_ctor_get(x_52, 3);
x_60 = lean_ctor_get(x_52, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_61 = l_Lean_Meta_getPropHyps(x_12, x_13, x_14, x_15, x_53);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_array_size(x_62);
x_65 = 0;
x_66 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_62, x_64, x_65, x_57, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_63);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_62);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_ctor_set(x_52, 1, x_68);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_52);
lean_ctor_set(x_69, 1, x_54);
lean_ctor_set(x_69, 2, x_5);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
lean_ctor_set(x_52, 1, x_70);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_52);
lean_ctor_set(x_72, 1, x_54);
lean_ctor_set(x_72, 2, x_5);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_52);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_5);
x_74 = !lean_is_exclusive(x_66);
if (x_74 == 0)
{
return x_66;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_66);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_free_object(x_52);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_61);
if (x_78 == 0)
{
return x_61;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_61, 0);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_61);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; uint32_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint32_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_52, 0);
x_83 = lean_ctor_get_uint32(x_52, sizeof(void*)*5);
x_84 = lean_ctor_get(x_52, 1);
x_85 = lean_ctor_get(x_52, 2);
x_86 = lean_ctor_get(x_52, 3);
x_87 = lean_ctor_get_uint32(x_52, sizeof(void*)*5 + 4);
x_88 = lean_ctor_get(x_52, 4);
x_89 = lean_ctor_get_uint8(x_52, sizeof(void*)*5 + 8);
lean_inc(x_88);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_82);
lean_dec(x_52);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_90 = l_Lean_Meta_getPropHyps(x_12, x_13, x_14, x_15, x_53);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_array_size(x_91);
x_94 = 0;
x_95 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_91, x_93, x_94, x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_92);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_91);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_99, 0, x_82);
lean_ctor_set(x_99, 1, x_96);
lean_ctor_set(x_99, 2, x_85);
lean_ctor_set(x_99, 3, x_86);
lean_ctor_set(x_99, 4, x_88);
lean_ctor_set_uint32(x_99, sizeof(void*)*5, x_83);
lean_ctor_set_uint32(x_99, sizeof(void*)*5 + 4, x_87);
lean_ctor_set_uint8(x_99, sizeof(void*)*5 + 8, x_89);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_54);
lean_ctor_set(x_100, 2, x_5);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_54);
lean_dec(x_5);
x_102 = lean_ctor_get(x_95, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_104 = x_95;
} else {
 lean_dec_ref(x_95);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_54);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_106 = lean_ctor_get(x_90, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_90, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_108 = x_90;
} else {
 lean_dec_ref(x_90);
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
else
{
uint8_t x_110; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_110 = !lean_is_exclusive(x_39);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_39, 0);
lean_dec(x_111);
x_112 = lean_ctor_get(x_40, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_40, 1);
lean_inc(x_113);
lean_dec(x_40);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_5);
lean_ctor_set(x_39, 0, x_114);
return x_39;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_39, 1);
lean_inc(x_115);
lean_dec(x_39);
x_116 = lean_ctor_get(x_40, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_40, 1);
lean_inc(x_117);
lean_dec(x_40);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_5);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_120 = !lean_is_exclusive(x_39);
if (x_120 == 0)
{
return x_39;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_39, 0);
x_122 = lean_ctor_get(x_39, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_39);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_23);
if (x_124 == 0)
{
return x_23;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_23, 0);
x_126 = lean_ctor_get(x_23, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_23);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_17, 0);
x_129 = lean_ctor_get(x_17, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_17);
x_130 = lean_unsigned_to_nat(1u);
x_131 = l_Lean_Syntax_getArg(x_1, x_130);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_132 = l_Lean_Elab_Tactic_elabSimpConfig(x_131, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint32_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint32_t x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_unsigned_to_nat(4u);
x_136 = l_Lean_Syntax_getArg(x_1, x_135);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
x_138 = l_UInt32_ofNatTruncate(x_137);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_3);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_array_mk(x_140);
x_142 = lean_box(0);
x_143 = 0;
x_144 = lean_unsigned_to_nat(0u);
x_145 = 0;
x_146 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_146, 0, x_133);
lean_ctor_set(x_146, 1, x_141);
lean_ctor_set(x_146, 2, x_128);
lean_ctor_set(x_146, 3, x_142);
lean_ctor_set(x_146, 4, x_144);
lean_ctor_set_uint32(x_146, sizeof(void*)*5, x_138);
lean_ctor_set_uint32(x_146, sizeof(void*)*5 + 4, x_143);
lean_ctor_set_uint8(x_146, sizeof(void*)*5 + 8, x_145);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_7);
lean_ctor_set(x_147, 1, x_139);
x_148 = lean_array_mk(x_147);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_149 = l_Lean_Elab_Tactic_elabSimpArgs(x_136, x_146, x_148, x_4, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_134);
lean_dec(x_136);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_150, sizeof(void*)*2);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_dec(x_150);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_156, 2, x_5);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
else
{
if (x_6 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint32_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint32_t x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; 
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
lean_dec(x_149);
x_160 = lean_ctor_get(x_150, 1);
lean_inc(x_160);
lean_dec(x_150);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get_uint32(x_158, sizeof(void*)*5);
x_163 = lean_ctor_get(x_158, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_158, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_158, 3);
lean_inc(x_165);
x_166 = lean_ctor_get_uint32(x_158, sizeof(void*)*5 + 4);
x_167 = lean_ctor_get(x_158, 4);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_158, sizeof(void*)*5 + 8);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 x_169 = x_158;
} else {
 lean_dec_ref(x_158);
 x_169 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_170 = l_Lean_Meta_getPropHyps(x_12, x_13, x_14, x_15, x_159);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_array_size(x_171);
x_174 = 0;
x_175 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_171, x_173, x_174, x_163, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_172);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_179 = lean_alloc_ctor(0, 5, 9);
} else {
 x_179 = x_169;
}
lean_ctor_set(x_179, 0, x_161);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_164);
lean_ctor_set(x_179, 3, x_165);
lean_ctor_set(x_179, 4, x_167);
lean_ctor_set_uint32(x_179, sizeof(void*)*5, x_162);
lean_ctor_set_uint32(x_179, sizeof(void*)*5 + 4, x_166);
lean_ctor_set_uint8(x_179, sizeof(void*)*5 + 8, x_168);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_160);
lean_ctor_set(x_180, 2, x_5);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_5);
x_182 = lean_ctor_get(x_175, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_184 = x_175;
} else {
 lean_dec_ref(x_175);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_186 = lean_ctor_get(x_170, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_170, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_188 = x_170;
} else {
 lean_dec_ref(x_170);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_190 = lean_ctor_get(x_149, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_191 = x_149;
} else {
 lean_dec_ref(x_149);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_150, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_150, 1);
lean_inc(x_193);
lean_dec(x_150);
x_194 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set(x_194, 2, x_5);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_196 = lean_ctor_get(x_149, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_149, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_198 = x_149;
} else {
 lean_dec_ref(x_149);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_128);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_200 = lean_ctor_get(x_132, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_132, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_202 = x_132;
} else {
 lean_dec_ref(x_132);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (x_6 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Lean_Meta_Simp_getSimprocs___rarg(x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Tactic_mkSimpContext___lambda__1(x_1, x_2, x_7, x_3, x_4, x_5, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__2;
x_22 = l_Lean_Elab_Tactic_mkSimpContext___lambda__1(x_1, x_2, x_7, x_3, x_4, x_5, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1;
x_3 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
x_4 = l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_2);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_inc(x_9);
x_18 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_41 = lean_unsigned_to_nat(3u);
x_42 = l_Lean_Syntax_getArg(x_1, x_41);
x_43 = l_Lean_Syntax_isNone(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = 1;
x_21 = x_44;
goto block_40;
}
else
{
uint8_t x_45; 
x_45 = 0;
x_21 = x_45;
goto block_40;
}
block_40:
{
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_14);
lean_inc(x_13);
x_22 = lean_apply_3(x_5, x_13, x_14, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Tactic_mkSimpContext___lambda__2(x_1, x_2, x_3, x_19, x_4, x_21, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
x_30 = l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__3;
x_31 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__6;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_32 = l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2(x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Tactic_mkSimpContext___lambda__2(x_1, x_2, x_3, x_19, x_4, x_21, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'dsimp' tactic does not support 'discharger' option", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; 
x_13 = 2;
x_14 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729_(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_apply_10(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__2;
x_18 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'simp_all' tactic does not support 'discharger' option", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_mkSimpContext___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_box(x_3);
x_16 = lean_box(x_2);
x_17 = lean_box(x_4);
lean_inc(x_5);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___lambda__3___boxed), 15, 5);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_5);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_isNone(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_1);
x_22 = 1;
x_23 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_beqSimpKind____x40_Lean_Elab_Tactic_Simp___hyg_1729_(x_3, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_mkSimpContext___lambda__4(x_3, x_18, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_18);
x_26 = l_Lean_Elab_Tactic_mkSimpContext___closed__2;
x_27 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Tactic_mkSimpContext___lambda__3(x_1, x_3, x_2, x_4, x_5, x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___at_Lean_Elab_Tactic_mkSimpContext___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Lean_Elab_Tactic_mkSimpContext___lambda__1(x_1, x_17, x_3, x_18, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_5);
lean_dec(x_5);
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Lean_Elab_Tactic_mkSimpContext___lambda__2(x_1, x_17, x_18, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = l_Lean_Elab_Tactic_mkSimpContext___lambda__3(x_1, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Elab_Tactic_mkSimpContext___lambda__4(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_15, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1;
x_3 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("When tracing is enabled, calls to `simp` or `dsimp` will print an equivalent `simp only` call.", 94, 94);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5;
x_3 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__1;
x_5 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1;
x_6 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__2;
x_7 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__3;
x_3 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__5;
x_4 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__7;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_4, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 7);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Lean_ResolveName_resolveGlobalName(x_10, x_11, x_12, x_1);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_4, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 7);
lean_inc(x_18);
lean_dec(x_4);
x_19 = l_Lean_ResolveName_resolveGlobalName(x_16, x_17, x_18, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_Name_appendCore(x_12, x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_15);
x_16 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(x_15, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_2);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_2);
{
lean_object* _tmp_2 = x_13;
lean_object* _tmp_3 = x_3;
lean_object* _tmp_8 = x_18;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_3);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_dec(x_27);
x_28 = lean_name_eq(x_26, x_1);
lean_dec(x_26);
if (x_28 == 0)
{
lean_free_object(x_16);
lean_inc(x_2);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 0, x_2);
x_3 = x_13;
x_4 = x_20;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_15);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_15);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 0, x_31);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_name_eq(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_free_object(x_16);
lean_inc(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_15);
x_3 = x_13;
x_4 = x_34;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_15);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_15);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_16, 0, x_38);
return x_16;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_dec(x_16);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_41 = x_20;
} else {
 lean_dec_ref(x_20);
 x_41 = lean_box(0);
}
x_42 = lean_name_eq(x_40, x_1);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_2);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_15);
x_3 = x_13;
x_4 = x_43;
x_9 = x_39;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_15);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_15);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_41)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_41;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_15);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_21, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_dec(x_16);
lean_inc(x_2);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 0, x_2);
x_3 = x_13;
x_4 = x_21;
x_9 = x_52;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_21);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_dec(x_16);
lean_inc(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_15);
x_3 = x_13;
x_4 = x_55;
x_9 = x_54;
goto _start;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_59 = lean_ctor_get(x_4, 1);
lean_inc(x_59);
lean_dec(x_4);
x_60 = l_Lean_Name_appendCore(x_57, x_59);
lean_dec(x_57);
lean_inc(x_7);
lean_inc(x_60);
x_61 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(x_60, x_5, x_6, x_7, x_8, x_9);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_60);
x_3 = x_58;
x_4 = x_64;
x_9 = x_63;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
x_72 = lean_name_eq(x_70, x_1);
lean_dec(x_70);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_69);
lean_inc(x_2);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_60);
x_3 = x_58;
x_4 = x_73;
x_9 = x_68;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_58);
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_60);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_60);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_60);
if (lean_is_scalar(x_69)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_69;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_68);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_66);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_79 = x_67;
} else {
 lean_dec_ref(x_67);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_dec(x_61);
lean_inc(x_2);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
 lean_ctor_set_tag(x_81, 0);
}
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_60);
x_3 = x_58;
x_4 = x_81;
x_9 = x_80;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Name_componentsRev(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1;
x_12 = l_List_forIn_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(x_2, x_10, x_9, x_11, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Name_hasMacroScopes(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_9);
x_15 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
lean_inc(x_2);
{
size_t _tmp_4 = x_19;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_17;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_32 = x_16;
} else {
 lean_dec_ref(x_16);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_getRevAliases(x_11, x_1);
lean_dec(x_11);
x_13 = lean_array_mk(x_12);
x_14 = l_Lean_rootNamespace;
lean_inc(x_1);
x_15 = l_Lean_Name_append(x_14, x_1);
x_16 = lean_array_push(x_13, x_15);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(x_1, x_19, x_16, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_11 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(x_2, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
lean_inc(x_21);
x_22 = lean_private_to_user_name(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = lean_name_eq(x_21, x_2);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_rootNamespace;
x_25 = l_Lean_Name_append(x_24, x_2);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_name_eq(x_26, x_2);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_rootNamespace;
x_29 = l_Lean_Name_append(x_28, x_2);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
else
{
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
lean_inc(x_31);
x_32 = lean_private_to_user_name(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = lean_name_eq(x_31, x_2);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_rootNamespace;
x_35 = l_Lean_Name_append(x_34, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_name_eq(x_38, x_2);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_rootNamespace;
x_41 = l_Lean_Name_append(x_40, x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_30);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_30);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_18);
lean_dec(x_17);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_11, 0);
lean_dec(x_45);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Name_hasMacroScopes(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__2(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_root_", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_name_eq(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__2;
x_12 = l_Lean_Name_append(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
lean_inc(x_1);
x_8 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Lean_LocalContext_usesUserName(x_12, x_10);
if (x_13 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_8);
x_14 = lean_box(0);
x_15 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1(x_10, x_1, x_14, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_5);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_ctor_get(x_3, 1);
x_19 = l_Lean_LocalContext_usesUserName(x_18, x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1(x_16, x_1, x_21, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_5);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_push(x_2, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = l_Lean_LocalDecl_userName(x_2);
lean_inc(x_17);
x_18 = lean_is_inaccessible_user_name(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Name_hasMacroScopes(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_LocalContext_findFromUserName_x3f(x_3, x_17);
x_21 = l_Lean_LocalDecl_fvarId(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4;
x_23 = l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(x_22);
x_24 = l_Lean_LocalDecl_fvarId(x_23);
lean_dec(x_23);
x_25 = lean_name_eq(x_24, x_21);
lean_dec(x_21);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_17);
lean_free_object(x_4);
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_4);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_4);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = l_Lean_LocalDecl_fvarId(x_35);
lean_dec(x_35);
x_37 = lean_name_eq(x_36, x_21);
lean_dec(x_21);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_10);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_array_push(x_16, x_17);
lean_ctor_set(x_20, 0, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_20);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_10);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
lean_dec(x_20);
x_47 = l_Lean_LocalDecl_fvarId(x_46);
lean_dec(x_46);
x_48 = lean_name_eq(x_47, x_21);
lean_dec(x_21);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_17);
lean_dec(x_16);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_10);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_array_push(x_16, x_17);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_17);
lean_free_object(x_4);
lean_dec(x_16);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_10);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_17);
lean_free_object(x_4);
lean_dec(x_16);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_10);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_4, 0);
lean_inc(x_66);
lean_dec(x_4);
x_67 = l_Lean_LocalDecl_userName(x_2);
lean_inc(x_67);
x_68 = lean_is_inaccessible_user_name(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = l_Lean_Name_hasMacroScopes(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lean_LocalContext_findFromUserName_x3f(x_3, x_67);
x_71 = l_Lean_LocalDecl_fvarId(x_2);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4;
x_73 = l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(x_72);
x_74 = l_Lean_LocalDecl_fvarId(x_73);
lean_dec(x_73);
x_75 = lean_name_eq(x_74, x_71);
lean_dec(x_71);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_67);
lean_dec(x_66);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_10);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_array_push(x_66, x_67);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_10);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_86 = x_70;
} else {
 lean_dec_ref(x_70);
 x_86 = lean_box(0);
}
x_87 = l_Lean_LocalDecl_fvarId(x_85);
lean_dec(x_85);
x_88 = lean_name_eq(x_87, x_71);
lean_dec(x_71);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_86);
lean_dec(x_67);
lean_dec(x_66);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_10);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_array_push(x_66, x_67);
if (lean_is_scalar(x_86)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_86;
}
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_10);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_67);
lean_dec(x_66);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_10);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_67);
lean_dec(x_66);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_10);
return x_105;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpPre", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("↓", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("patternIgnore", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("←", 3, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_5, x_7);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_86; uint8_t x_270; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_27 = x_8;
} else {
 lean_dec_ref(x_8);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_30 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
lean_inc(x_4);
x_270 = l_Lean_Environment_contains(x_4, x_28);
if (x_270 == 0)
{
lean_object* x_271; 
x_271 = lean_box(0);
x_31 = x_271;
goto block_85;
}
else
{
if (x_30 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4;
lean_inc(x_2);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_2);
x_274 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2;
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_28, x_275);
lean_dec(x_275);
if (x_276 == 0)
{
uint8_t x_277; 
x_277 = l_Lean_Meta_Match_isMatchEqnTheorem(x_4, x_28);
if (x_277 == 0)
{
lean_object* x_278; 
lean_dec(x_27);
x_278 = lean_box(0);
x_86 = x_278;
goto block_269;
}
else
{
lean_object* x_279; 
x_279 = lean_box(0);
x_31 = x_279;
goto block_85;
}
}
else
{
lean_object* x_280; 
x_280 = lean_box(0);
x_31 = x_280;
goto block_85;
}
}
else
{
uint8_t x_281; 
x_281 = l_Lean_Meta_Match_isMatchEqnTheorem(x_4, x_28);
if (x_281 == 0)
{
lean_object* x_282; 
lean_dec(x_27);
x_282 = lean_box(0);
x_86 = x_282;
goto block_269;
}
else
{
lean_object* x_283; 
x_283 = lean_box(0);
x_31 = x_283;
goto block_85;
}
}
}
block_85:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_31);
x_32 = l_Lean_Meta_Simp_isBuiltinSimproc(x_28, x_11, x_12, x_13);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_28);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
if (lean_is_scalar(x_27)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_27;
}
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_32, 0, x_38);
x_17 = x_32;
goto block_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_27;
}
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_26);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_17 = x_42;
goto block_24;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_mk_syntax_ident(x_28);
if (x_29 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_11, 5);
lean_inc(x_45);
x_46 = 0;
x_47 = l_Lean_SourceInfo_fromRef(x_45, x_46);
lean_dec(x_45);
x_48 = lean_st_ref_get(x_12, x_43);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_48, 1);
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_47);
lean_ctor_set_tag(x_48, 2);
lean_ctor_set(x_48, 1, x_52);
lean_ctor_set(x_48, 0, x_47);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_47);
x_54 = l_Lean_Syntax_node1(x_47, x_53, x_48);
x_55 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_47);
x_56 = l_Lean_Syntax_node1(x_47, x_55, x_54);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_47);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_57);
x_59 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_60 = l_Lean_Syntax_node3(x_47, x_59, x_56, x_58, x_44);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_60, x_9, x_10, x_11, x_12, x_50);
x_17 = x_61;
goto block_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_dec(x_48);
x_63 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_47);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_47);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_47);
x_66 = l_Lean_Syntax_node1(x_47, x_65, x_64);
x_67 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_47);
x_68 = l_Lean_Syntax_node1(x_47, x_67, x_66);
x_69 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_47);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_47);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_69);
x_71 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_72 = l_Lean_Syntax_node3(x_47, x_71, x_68, x_70, x_44);
x_73 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_72, x_9, x_10, x_11, x_12, x_62);
x_17 = x_73;
goto block_24;
}
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_11, 5);
lean_inc(x_74);
x_75 = 0;
x_76 = l_Lean_SourceInfo_fromRef(x_74, x_75);
lean_dec(x_74);
x_77 = lean_st_ref_get(x_12, x_43);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_80 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_76);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_80);
x_82 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
lean_inc(x_81);
x_83 = l_Lean_Syntax_node3(x_76, x_82, x_81, x_81, x_44);
x_84 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_83, x_9, x_10, x_11, x_12, x_78);
x_17 = x_84;
goto block_24;
}
}
}
block_269:
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_86);
x_87 = 0;
lean_inc(x_11);
x_88 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1(x_28, x_87, x_9, x_10, x_11, x_12, x_13);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_12, x_90);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 1);
x_94 = lean_ctor_get(x_91, 0);
lean_dec(x_94);
x_95 = lean_mk_syntax_ident(x_89);
if (x_29 == 0)
{
if (x_30 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_free_object(x_91);
x_96 = lean_ctor_get(x_11, 5);
lean_inc(x_96);
x_97 = l_Lean_SourceInfo_fromRef(x_96, x_87);
lean_dec(x_96);
x_98 = lean_st_ref_get(x_12, x_93);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_100 = lean_ctor_get(x_98, 1);
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
x_102 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_97);
lean_ctor_set_tag(x_98, 2);
lean_ctor_set(x_98, 1, x_102);
lean_ctor_set(x_98, 0, x_97);
x_103 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_97);
x_104 = l_Lean_Syntax_node1(x_97, x_103, x_98);
x_105 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_97);
x_106 = l_Lean_Syntax_node1(x_97, x_105, x_104);
x_107 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_97);
x_108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_108, 2, x_107);
x_109 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_110 = l_Lean_Syntax_node3(x_97, x_109, x_106, x_108, x_95);
x_111 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_110, x_9, x_10, x_11, x_12, x_100);
x_17 = x_111;
goto block_24;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
lean_dec(x_98);
x_113 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_97);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_97);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_97);
x_116 = l_Lean_Syntax_node1(x_97, x_115, x_114);
x_117 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_97);
x_118 = l_Lean_Syntax_node1(x_97, x_117, x_116);
x_119 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_97);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_97);
lean_ctor_set(x_120, 1, x_117);
lean_ctor_set(x_120, 2, x_119);
x_121 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_122 = l_Lean_Syntax_node3(x_97, x_121, x_118, x_120, x_95);
x_123 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_122, x_9, x_10, x_11, x_12, x_112);
x_17 = x_123;
goto block_24;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_11, 5);
lean_inc(x_124);
x_125 = l_Lean_SourceInfo_fromRef(x_124, x_87);
lean_dec(x_124);
x_126 = lean_st_ref_get(x_12, x_93);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_128 = lean_ctor_get(x_126, 1);
x_129 = lean_ctor_get(x_126, 0);
lean_dec(x_129);
x_130 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_125);
lean_ctor_set_tag(x_126, 2);
lean_ctor_set(x_126, 1, x_130);
lean_ctor_set(x_126, 0, x_125);
x_131 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_125);
x_132 = l_Lean_Syntax_node1(x_125, x_131, x_126);
x_133 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_125);
x_134 = l_Lean_Syntax_node1(x_125, x_133, x_132);
x_135 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_125);
lean_ctor_set_tag(x_91, 2);
lean_ctor_set(x_91, 1, x_135);
lean_ctor_set(x_91, 0, x_125);
x_136 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_125);
x_137 = l_Lean_Syntax_node1(x_125, x_136, x_91);
x_138 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_125);
x_139 = l_Lean_Syntax_node1(x_125, x_138, x_137);
lean_inc(x_125);
x_140 = l_Lean_Syntax_node1(x_125, x_133, x_139);
x_141 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_142 = l_Lean_Syntax_node3(x_125, x_141, x_134, x_140, x_95);
x_143 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_142, x_9, x_10, x_11, x_12, x_128);
x_17 = x_143;
goto block_24;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_144 = lean_ctor_get(x_126, 1);
lean_inc(x_144);
lean_dec(x_126);
x_145 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_125);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_125);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_125);
x_148 = l_Lean_Syntax_node1(x_125, x_147, x_146);
x_149 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_125);
x_150 = l_Lean_Syntax_node1(x_125, x_149, x_148);
x_151 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_125);
lean_ctor_set_tag(x_91, 2);
lean_ctor_set(x_91, 1, x_151);
lean_ctor_set(x_91, 0, x_125);
x_152 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_125);
x_153 = l_Lean_Syntax_node1(x_125, x_152, x_91);
x_154 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_125);
x_155 = l_Lean_Syntax_node1(x_125, x_154, x_153);
lean_inc(x_125);
x_156 = l_Lean_Syntax_node1(x_125, x_149, x_155);
x_157 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_158 = l_Lean_Syntax_node3(x_125, x_157, x_150, x_156, x_95);
x_159 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_158, x_9, x_10, x_11, x_12, x_144);
x_17 = x_159;
goto block_24;
}
}
}
else
{
lean_free_object(x_91);
if (x_30 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_160 = lean_ctor_get(x_11, 5);
lean_inc(x_160);
x_161 = l_Lean_SourceInfo_fromRef(x_160, x_87);
lean_dec(x_160);
x_162 = lean_st_ref_get(x_12, x_93);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_165 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_161);
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set(x_166, 2, x_165);
x_167 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
lean_inc(x_166);
x_168 = l_Lean_Syntax_node3(x_161, x_167, x_166, x_166, x_95);
x_169 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_168, x_9, x_10, x_11, x_12, x_163);
x_17 = x_169;
goto block_24;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_11, 5);
lean_inc(x_170);
x_171 = l_Lean_SourceInfo_fromRef(x_170, x_87);
lean_dec(x_170);
x_172 = lean_st_ref_get(x_12, x_93);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_174 = lean_ctor_get(x_172, 1);
x_175 = lean_ctor_get(x_172, 0);
lean_dec(x_175);
x_176 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_177 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_171);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_176);
lean_ctor_set(x_178, 2, x_177);
x_179 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_171);
lean_ctor_set_tag(x_172, 2);
lean_ctor_set(x_172, 1, x_179);
lean_ctor_set(x_172, 0, x_171);
x_180 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_171);
x_181 = l_Lean_Syntax_node1(x_171, x_180, x_172);
x_182 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_171);
x_183 = l_Lean_Syntax_node1(x_171, x_182, x_181);
lean_inc(x_171);
x_184 = l_Lean_Syntax_node1(x_171, x_176, x_183);
x_185 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_186 = l_Lean_Syntax_node3(x_171, x_185, x_178, x_184, x_95);
x_187 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_186, x_9, x_10, x_11, x_12, x_174);
x_17 = x_187;
goto block_24;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_188 = lean_ctor_get(x_172, 1);
lean_inc(x_188);
lean_dec(x_172);
x_189 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_190 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_171);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_171);
lean_ctor_set(x_191, 1, x_189);
lean_ctor_set(x_191, 2, x_190);
x_192 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_171);
x_193 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_193, 0, x_171);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_171);
x_195 = l_Lean_Syntax_node1(x_171, x_194, x_193);
x_196 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_171);
x_197 = l_Lean_Syntax_node1(x_171, x_196, x_195);
lean_inc(x_171);
x_198 = l_Lean_Syntax_node1(x_171, x_189, x_197);
x_199 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_200 = l_Lean_Syntax_node3(x_171, x_199, x_191, x_198, x_95);
x_201 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_200, x_9, x_10, x_11, x_12, x_188);
x_17 = x_201;
goto block_24;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_91, 1);
lean_inc(x_202);
lean_dec(x_91);
x_203 = lean_mk_syntax_ident(x_89);
if (x_29 == 0)
{
if (x_30 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_204 = lean_ctor_get(x_11, 5);
lean_inc(x_204);
x_205 = l_Lean_SourceInfo_fromRef(x_204, x_87);
lean_dec(x_204);
x_206 = lean_st_ref_get(x_12, x_202);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_205);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(2, 2, 0);
} else {
 x_210 = x_208;
 lean_ctor_set_tag(x_210, 2);
}
lean_ctor_set(x_210, 0, x_205);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_205);
x_212 = l_Lean_Syntax_node1(x_205, x_211, x_210);
x_213 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_205);
x_214 = l_Lean_Syntax_node1(x_205, x_213, x_212);
x_215 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_205);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_205);
lean_ctor_set(x_216, 1, x_213);
lean_ctor_set(x_216, 2, x_215);
x_217 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_218 = l_Lean_Syntax_node3(x_205, x_217, x_214, x_216, x_203);
x_219 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_218, x_9, x_10, x_11, x_12, x_207);
x_17 = x_219;
goto block_24;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_220 = lean_ctor_get(x_11, 5);
lean_inc(x_220);
x_221 = l_Lean_SourceInfo_fromRef(x_220, x_87);
lean_dec(x_220);
x_222 = lean_st_ref_get(x_12, x_202);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_221);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(2, 2, 0);
} else {
 x_226 = x_224;
 lean_ctor_set_tag(x_226, 2);
}
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_221);
x_228 = l_Lean_Syntax_node1(x_221, x_227, x_226);
x_229 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_221);
x_230 = l_Lean_Syntax_node1(x_221, x_229, x_228);
x_231 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_221);
x_232 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_232, 0, x_221);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_221);
x_234 = l_Lean_Syntax_node1(x_221, x_233, x_232);
x_235 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_221);
x_236 = l_Lean_Syntax_node1(x_221, x_235, x_234);
lean_inc(x_221);
x_237 = l_Lean_Syntax_node1(x_221, x_229, x_236);
x_238 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_239 = l_Lean_Syntax_node3(x_221, x_238, x_230, x_237, x_203);
x_240 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_239, x_9, x_10, x_11, x_12, x_223);
x_17 = x_240;
goto block_24;
}
}
else
{
if (x_30 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_241 = lean_ctor_get(x_11, 5);
lean_inc(x_241);
x_242 = l_Lean_SourceInfo_fromRef(x_241, x_87);
lean_dec(x_241);
x_243 = lean_st_ref_get(x_12, x_202);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_246 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_242);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_242);
lean_ctor_set(x_247, 1, x_245);
lean_ctor_set(x_247, 2, x_246);
x_248 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
lean_inc(x_247);
x_249 = l_Lean_Syntax_node3(x_242, x_248, x_247, x_247, x_203);
x_250 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_249, x_9, x_10, x_11, x_12, x_244);
x_17 = x_250;
goto block_24;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_251 = lean_ctor_get(x_11, 5);
lean_inc(x_251);
x_252 = l_Lean_SourceInfo_fromRef(x_251, x_87);
lean_dec(x_251);
x_253 = lean_st_ref_get(x_12, x_202);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_257 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_252);
x_258 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_258, 0, x_252);
lean_ctor_set(x_258, 1, x_256);
lean_ctor_set(x_258, 2, x_257);
x_259 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_252);
if (lean_is_scalar(x_255)) {
 x_260 = lean_alloc_ctor(2, 2, 0);
} else {
 x_260 = x_255;
 lean_ctor_set_tag(x_260, 2);
}
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_252);
x_262 = l_Lean_Syntax_node1(x_252, x_261, x_260);
x_263 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_252);
x_264 = l_Lean_Syntax_node1(x_252, x_263, x_262);
lean_inc(x_252);
x_265 = l_Lean_Syntax_node1(x_252, x_256, x_264);
x_266 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_267 = l_Lean_Syntax_node3(x_252, x_266, x_258, x_265, x_203);
x_268 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_26, x_25, x_267, x_9, x_10, x_11, x_12, x_254);
x_17 = x_268;
goto block_24;
}
}
}
}
}
case 1:
{
uint8_t x_284; 
x_284 = !lean_is_exclusive(x_8);
if (x_284 == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_16);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_8, 0);
x_287 = lean_ctor_get(x_8, 1);
x_288 = lean_ctor_get(x_16, 0);
lean_inc(x_3);
x_289 = lean_local_ctx_find(x_3, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; 
lean_ctor_set(x_16, 0, x_8);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_16);
lean_ctor_set(x_290, 1, x_13);
x_17 = x_290;
goto block_24;
}
else
{
lean_free_object(x_16);
if (x_1 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_free_object(x_8);
x_291 = lean_ctor_get(x_289, 0);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_box(0);
x_293 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_286, x_291, x_3, x_287, x_292, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_291);
x_17 = x_293;
goto block_24;
}
else
{
uint8_t x_294; 
x_294 = !lean_is_exclusive(x_289);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_289, 0);
x_296 = l_Lean_LocalDecl_hasValue(x_295);
if (x_296 == 0)
{
lean_object* x_297; 
lean_dec(x_295);
lean_ctor_set(x_289, 0, x_8);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_289);
lean_ctor_set(x_297, 1, x_13);
x_17 = x_297;
goto block_24;
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_free_object(x_289);
lean_free_object(x_8);
x_298 = lean_box(0);
x_299 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_286, x_295, x_3, x_287, x_298, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_295);
x_17 = x_299;
goto block_24;
}
}
else
{
lean_object* x_300; uint8_t x_301; 
x_300 = lean_ctor_get(x_289, 0);
lean_inc(x_300);
lean_dec(x_289);
x_301 = l_Lean_LocalDecl_hasValue(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
lean_dec(x_300);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_8);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_13);
x_17 = x_303;
goto block_24;
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_free_object(x_8);
x_304 = lean_box(0);
x_305 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_286, x_300, x_3, x_287, x_304, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_300);
x_17 = x_305;
goto block_24;
}
}
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_8, 0);
x_307 = lean_ctor_get(x_8, 1);
x_308 = lean_ctor_get(x_16, 0);
lean_inc(x_308);
lean_dec(x_16);
lean_inc(x_3);
x_309 = lean_local_ctx_find(x_3, x_308);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_8);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_13);
x_17 = x_311;
goto block_24;
}
else
{
if (x_1 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_free_object(x_8);
x_312 = lean_ctor_get(x_309, 0);
lean_inc(x_312);
lean_dec(x_309);
x_313 = lean_box(0);
x_314 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_306, x_312, x_3, x_307, x_313, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_312);
x_17 = x_314;
goto block_24;
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_315 = lean_ctor_get(x_309, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_316 = x_309;
} else {
 lean_dec_ref(x_309);
 x_316 = lean_box(0);
}
x_317 = l_Lean_LocalDecl_hasValue(x_315);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_315);
if (lean_is_scalar(x_316)) {
 x_318 = lean_alloc_ctor(1, 1, 0);
} else {
 x_318 = x_316;
}
lean_ctor_set(x_318, 0, x_8);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_13);
x_17 = x_319;
goto block_24;
}
else
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_316);
lean_free_object(x_8);
x_320 = lean_box(0);
x_321 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_306, x_315, x_3, x_307, x_320, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_315);
x_17 = x_321;
goto block_24;
}
}
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_8, 0);
x_323 = lean_ctor_get(x_8, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_8);
x_324 = lean_ctor_get(x_16, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_325 = x_16;
} else {
 lean_dec_ref(x_16);
 x_325 = lean_box(0);
}
lean_inc(x_3);
x_326 = lean_local_ctx_find(x_3, x_324);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_322);
lean_ctor_set(x_327, 1, x_323);
if (lean_is_scalar(x_325)) {
 x_328 = lean_alloc_ctor(1, 1, 0);
} else {
 x_328 = x_325;
}
lean_ctor_set(x_328, 0, x_327);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_13);
x_17 = x_329;
goto block_24;
}
else
{
lean_dec(x_325);
if (x_1 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_326, 0);
lean_inc(x_330);
lean_dec(x_326);
x_331 = lean_box(0);
x_332 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_322, x_330, x_3, x_323, x_331, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_330);
x_17 = x_332;
goto block_24;
}
else
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_333 = lean_ctor_get(x_326, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_334 = x_326;
} else {
 lean_dec_ref(x_326);
 x_334 = lean_box(0);
}
x_335 = l_Lean_LocalDecl_hasValue(x_333);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_333);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_322);
lean_ctor_set(x_336, 1, x_323);
if (lean_is_scalar(x_334)) {
 x_337 = lean_alloc_ctor(1, 1, 0);
} else {
 x_337 = x_334;
}
lean_ctor_set(x_337, 0, x_336);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_13);
x_17 = x_338;
goto block_24;
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_334);
x_339 = lean_box(0);
x_340 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_322, x_333, x_3, x_323, x_339, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_333);
x_17 = x_340;
goto block_24;
}
}
}
}
}
case 2:
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_8);
if (x_341 == 0)
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_16);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_343 = lean_ctor_get(x_8, 0);
x_344 = lean_ctor_get(x_16, 1);
x_345 = lean_ctor_get(x_16, 0);
lean_dec(x_345);
x_346 = lean_array_push(x_343, x_344);
lean_ctor_set(x_8, 0, x_346);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_8);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 0, x_347);
x_17 = x_16;
goto block_24;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_348 = lean_ctor_get(x_8, 0);
x_349 = lean_ctor_get(x_16, 1);
lean_inc(x_349);
lean_dec(x_16);
x_350 = lean_array_push(x_348, x_349);
lean_ctor_set(x_8, 0, x_350);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_8);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_13);
x_17 = x_352;
goto block_24;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_353 = lean_ctor_get(x_8, 0);
x_354 = lean_ctor_get(x_8, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_8);
x_355 = lean_ctor_get(x_16, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_356 = x_16;
} else {
 lean_dec_ref(x_16);
 x_356 = lean_box(0);
}
x_357 = lean_array_push(x_353, x_355);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_354);
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_358);
if (lean_is_scalar(x_356)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_356;
 lean_ctor_set_tag(x_360, 0);
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_13);
x_17 = x_360;
goto block_24;
}
}
default: 
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_16);
if (x_361 == 0)
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_ctor_get(x_16, 0);
lean_dec(x_362);
x_363 = !lean_is_exclusive(x_8);
if (x_363 == 0)
{
lean_object* x_364; 
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_8);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_16);
lean_ctor_set(x_364, 1, x_13);
x_17 = x_364;
goto block_24;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_8, 0);
x_366 = lean_ctor_get(x_8, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_8);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_367);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_16);
lean_ctor_set(x_368, 1, x_13);
x_17 = x_368;
goto block_24;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_16);
x_369 = lean_ctor_get(x_8, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_8, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_371 = x_8;
} else {
 lean_dec_ref(x_8);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_13);
x_17 = x_374;
goto block_24;
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_20;
x_13 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_ctor_get(x_6, 5);
x_15 = 0;
x_16 = l_Lean_SourceInfo_fromRef(x_14, x_15);
x_17 = lean_st_ref_get(x_7, x_8);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_16);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_syntax_ident(x_11);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
lean_inc(x_21);
x_24 = l_Lean_Syntax_node3(x_16, x_23, x_21, x_21, x_22);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_13, x_2, x_24);
x_2 = x_26;
x_3 = x_27;
x_8 = x_18;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_12 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__4;
x_13 = l_Lean_Syntax_mkSep(x_4, x_12);
x_14 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__6;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_array_mk(x_18);
x_20 = lean_box(2);
x_21 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_Syntax_setArg(x_2, x_23, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_26 = lean_box(2);
x_27 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_3);
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_Syntax_setArg(x_2, x_29, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_2 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Simp_UsedSimps_toArray(x_1);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2;
lean_inc(x_7);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(x_2, x_10, x_11, x_15, x_16, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_7, 5);
lean_inc(x_25);
x_26 = 0;
x_27 = l_Lean_SourceInfo_fromRef(x_25, x_26);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_8, x_23);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3;
lean_inc(x_27);
lean_ctor_set_tag(x_28, 2);
lean_ctor_set(x_28, 1, x_32);
lean_ctor_set(x_28, 0, x_27);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
x_34 = l_Lean_Syntax_node1(x_27, x_33, x_28);
x_35 = lean_array_push(x_24, x_34);
x_36 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(x_10, x_3, x_36, x_35, x_37, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3;
lean_inc(x_27);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_27);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
x_43 = l_Lean_Syntax_node1(x_27, x_42, x_41);
x_44 = lean_array_push(x_24, x_43);
x_45 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(x_10, x_3, x_45, x_44, x_46, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_44);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_dec(x_20);
x_49 = lean_ctor_get(x_21, 0);
lean_inc(x_49);
lean_dec(x_21);
x_50 = lean_ctor_get(x_22, 0);
lean_inc(x_50);
lean_dec(x_22);
x_51 = lean_array_size(x_50);
x_52 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8(x_51, x_18, x_50, x_5, x_6, x_7, x_8, x_48);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Array_append___rarg(x_49, x_53);
lean_dec(x_53);
x_56 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_57 = lean_box(0);
x_58 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(x_10, x_3, x_56, x_55, x_57, x_5, x_6, x_7, x_8, x_54);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_55);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAll", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_mkSimpOnly___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_mkSimpOnly___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkSimpOnly___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_mkSimpOnly___closed__5;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_3 = l_Lean_Elab_Tactic_mkSimpOnly___closed__6;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Elab_Tactic_mkSimpOnly___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isNone(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2(x_2, x_9, x_1, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Elab_Tactic_mkSimpOnly___closed__7;
x_16 = l_Lean_Syntax_setArg(x_1, x_10, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2(x_2, x_9, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(x_14, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_mkSimpOnly(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_traceSimpCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_traceSimpCall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_traceSimpCall___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Elab_Tactic_mkSimpOnly(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_MessageData_ofSyntax(x_10);
x_15 = l_Lean_Elab_Tactic_traceSimpCall___closed__2;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_15);
x_16 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
x_18 = 0;
x_19 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_13, x_17, x_18, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_3);
lean_dec(x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
lean_dec(x_1);
x_24 = l_Lean_MessageData_ofSyntax(x_20);
x_25 = l_Lean_Elab_Tactic_traceSimpCall___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = 0;
x_30 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_23, x_28, x_29, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_3);
lean_dec(x_23);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpLocation_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpLocation_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpLocation_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_simpLocation_go___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpLocation_go___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Tactic_simpLocation_go___closed__3;
x_3 = l_Lean_Elab_Tactic_simpLocation_go___closed__2;
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
static lean_object* _init_l_Lean_Elab_Tactic_simpLocation_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2;
x_2 = l_Lean_Elab_Tactic_simpLocation_go___closed__4;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpLocation_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_simpLocation_go___closed__1;
x_2 = l_Lean_Elab_Tactic_simpLocation_go___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_simpLocation_go___closed__6;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_19 = l_Lean_Meta_simpGoal(x_16, x_1, x_2, x_3, x_5, x_4, x_18, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_replaceMainGoal(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_23);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_ctor_get(x_34, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_40);
lean_ctor_set(x_34, 0, x_38);
x_41 = l_Lean_Elab_Tactic_replaceMainGoal(x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_36);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_36);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Tactic_replaceMainGoal(x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_36);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_simpLocation_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Tactic_simpLocation_go(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_MVarId_getNondepPropHyps(x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = l_Lean_Elab_Tactic_simpLocation_go(x_1, x_2, x_3, x_17, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_Tactic_getFVarIds(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_simpLocation_go(x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
uint8_t x_19; 
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
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocation___lambda__1___boxed), 12, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
x_15 = l_Lean_Elab_Tactic_withMainContext___rarg(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_18 = lean_box(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocation___lambda__2___boxed), 14, 5);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_18);
x_20 = l_Lean_Elab_Tactic_withMainContext___rarg(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_simpLocation___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Tactic_simpLocation___lambda__2(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_reportDiag(x_12, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(5u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_expandOptLocation(x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_simpLocation(x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
static lean_object* _init_l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tactic_simp_trace;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 0;
x_12 = 0;
x_13 = l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_11, x_12, x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp___lambda__1___boxed), 13, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_8, 2);
lean_inc(x_24);
x_25 = l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2;
x_26 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_evalSimp___lambda__2(x_22, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_22);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_inc(x_8);
lean_inc(x_6);
x_30 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_29, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_evalSimp___lambda__2(x_22, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_31);
lean_dec(x_22);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp___lambda__3), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Elab_Tactic_withMainContext___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalSimp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalSimp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimp", 8, 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(432u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(438u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(432u);
x_2 = lean_unsigned_to_nat(46u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(432u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(54u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
x_14 = l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Tactic_evalSimp___lambda__2(x_1, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_8);
x_19 = l_Lean_Elab_Tactic_traceSimpCall(x_2, x_18, x_8, x_9, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Tactic_evalSimp___lambda__2(x_1, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Elab_Tactic_mkSimpContext(x_1, x_11, x_12, x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Tactic_simpLocation_go___closed__6;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_simpAll(x_20, x_17, x_18, x_22, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_replaceMainGoal(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Tactic_evalSimpAll___lambda__1(x_27, x_1, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_30);
lean_dec(x_27);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_24, 1);
x_40 = lean_ctor_get(x_24, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec(x_25);
x_42 = lean_box(0);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_42);
lean_ctor_set(x_24, 0, x_41);
x_43 = l_Lean_Elab_Tactic_replaceMainGoal(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Tactic_evalSimpAll___lambda__1(x_39, x_1, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_44);
lean_dec(x_39);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_dec(x_24);
x_52 = lean_ctor_get(x_25, 0);
lean_inc(x_52);
lean_dec(x_25);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Tactic_replaceMainGoal(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Tactic_evalSimpAll___lambda__1(x_51, x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_56);
lean_dec(x_51);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_23);
if (x_63 == 0)
{
return x_23;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_23, 0);
x_65 = lean_ctor_get(x_23, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_23);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_19);
if (x_67 == 0)
{
return x_19;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_19, 0);
x_69 = lean_ctor_get(x_19, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_19);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_14);
if (x_71 == 0)
{
return x_14;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_14, 0);
x_73 = lean_ctor_get(x_14, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_14);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAll___lambda__2), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Elab_Tactic_withMainContext___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalSimpAll___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpAll", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAll), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4;
x_3 = l_Lean_Elab_Tactic_mkSimpOnly___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(440u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(448u);
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(45u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(19u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(440u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(440u);
x_2 = lean_unsigned_to_nat(60u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(49u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(60u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_traceSimpCall(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
x_14 = l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Tactic_evalSimp___lambda__2(x_1, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1___boxed), 11, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_evalSimp___lambda__2(x_1, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_22);
lean_dec(x_1);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_simpLocation_go___closed__6;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_15);
x_18 = l_Lean_Meta_dsimpGoal(x_15, x_1, x_2, x_3, x_4, x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_replaceMainGoal(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2(x_22, x_15, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_19, 1);
x_35 = lean_ctor_get(x_19, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_20, 0);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_37);
lean_ctor_set(x_19, 0, x_36);
x_38 = l_Lean_Elab_Tactic_replaceMainGoal(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2(x_34, x_15, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
lean_dec(x_39);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_ctor_get(x_20, 0);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Tactic_replaceMainGoal(x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2(x_46, x_15, x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_52);
lean_dec(x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_46);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_56 = x_50;
} else {
 lean_dec_ref(x_50);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
return x_14;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_14, 0);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_14);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3___boxed), 13, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_3);
x_16 = l_Lean_Elab_Tactic_withSimpDiagnostics(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_MVarId_getNondepPropHyps(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = l_Lean_Elab_Tactic_dsimpLocation_go(x_1, x_2, x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_19;
}
else
{
uint8_t x_20; 
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
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
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
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_getFVarIds(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_dsimpLocation_go(x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_17;
}
else
{
uint8_t x_18; 
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
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation___lambda__1), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Tactic_withMainContext___rarg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_dec(x_3);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation___lambda__2___boxed), 13, 4);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_Elab_Tactic_withMainContext___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation___lambda__2(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = 0;
x_12 = 2;
x_13 = l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1;
x_14 = lean_box(x_11);
x_15 = lean_box(x_12);
x_16 = lean_box(x_11);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_unsigned_to_nat(5u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
lean_dec(x_1);
x_25 = l_Lean_Elab_Tactic_expandOptLocation(x_24);
lean_dec(x_24);
x_26 = l_Lean_Elab_Tactic_dsimpLocation(x_21, x_22, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_26;
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimp", 5, 5);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDSimp", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimp), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(470u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(472u);
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(43u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(55u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(470u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(470u);
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(56u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = l_Lean_Syntax_TSepArray_getElems___rarg(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = l_Lean_Syntax_TSepArray_getElems___rarg(x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_BuiltinNotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_BuiltinNotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__3 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__3);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__5);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__2);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__3);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__4);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__6);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__1);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___closed__2);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___closed__1);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__1);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__2);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__3);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__4);
l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__5);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__1 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2);
l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___closed__1);
l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__1);
l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__2);
l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__3);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__1 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__2);
l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1);
l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__1);
l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__2);
l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__3);
l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___closed__1 = _init_l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___closed__1);
l_Lean_Elab_Tactic_instInhabitedSimpKind = _init_l_Lean_Elab_Tactic_instInhabitedSimpKind();
l_Lean_Elab_Tactic_instBEqSimpKind___closed__1 = _init_l_Lean_Elab_Tactic_instBEqSimpKind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instBEqSimpKind___closed__1);
l_Lean_Elab_Tactic_instBEqSimpKind = _init_l_Lean_Elab_Tactic_instBEqSimpKind();
lean_mark_persistent(l_Lean_Elab_Tactic_instBEqSimpKind);
l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1);
l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__2);
l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__3);
l_Lean_Elab_Tactic_tacticToDischarge___closed__1 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__1);
l_Lean_Elab_Tactic_tacticToDischarge___closed__2 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__2);
l_Lean_Elab_Tactic_tacticToDischarge___closed__3 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__3);
l_Lean_Elab_Tactic_tacticToDischarge___closed__4 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__4);
l_Lean_Elab_Tactic_tacticToDischarge___closed__5 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__5);
l_Lean_Elab_Tactic_tacticToDischarge___closed__6 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__6);
l_Lean_Elab_Tactic_tacticToDischarge___closed__7 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__7);
l_Lean_Elab_Tactic_tacticToDischarge___closed__8 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__8);
l_Lean_Elab_Tactic_tacticToDischarge___closed__9 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__9);
l_Lean_Elab_Tactic_tacticToDischarge___closed__10 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__10);
l_Lean_Elab_Tactic_tacticToDischarge___closed__11 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__11);
l_Lean_Elab_Tactic_tacticToDischarge___closed__12 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__12);
l_Lean_Elab_Tactic_tacticToDischarge___closed__13 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__13);
l_Lean_Elab_Tactic_tacticToDischarge___closed__14 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__14);
l_Lean_Elab_Tactic_tacticToDischarge___closed__15 = _init_l_Lean_Elab_Tactic_tacticToDischarge___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticToDischarge___closed__15);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__2 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__2);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__3 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__3);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__4 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__4);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__5);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__6 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__6);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__7 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__7);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__8 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__8);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__9 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__9);
l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__1);
l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__2 = _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__2);
l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3 = _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3);
l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__4 = _init_l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__4);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__3);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__4 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__4();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___closed__4);
l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___closed__1 = _init_l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___closed__1();
lean_mark_persistent(l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5___closed__1);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__1 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__1);
l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__2 = _init_l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8);
l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1 = _init_l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1);
l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__1 = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__1);
l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2 = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2);
l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__3 = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__3);
l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4 = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4);
l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__5 = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__5);
l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__6 = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__6);
l_Lean_Elab_Tactic_simpOnlyBuiltins = _init_l_Lean_Elab_Tactic_simpOnlyBuiltins();
lean_mark_persistent(l_Lean_Elab_Tactic_simpOnlyBuiltins);
l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1);
l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__2);
l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__1);
l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2);
l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__3);
l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__1);
l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__2);
l_Lean_Elab_Tactic_mkSimpContext___closed__1 = _init_l_Lean_Elab_Tactic_mkSimpContext___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___closed__1);
l_Lean_Elab_Tactic_mkSimpContext___closed__2 = _init_l_Lean_Elab_Tactic_mkSimpContext___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpContext___closed__2);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__1 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__1);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__2 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__2);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__3 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__3);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__4 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__4);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__5 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__5);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__6);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__7 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286____closed__7);
if (builtin) {res = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6286_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tactic_simp_trace = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tactic_simp_trace);
lean_dec_ref(res);
}l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1 = _init_l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1);
l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1 = _init_l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1);
l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__1 = _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__1);
l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__2 = _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__1);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__2);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__3);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__4);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__5);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__6);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__1);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2);
l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3);
l_Lean_Elab_Tactic_mkSimpOnly___closed__1 = _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___closed__1);
l_Lean_Elab_Tactic_mkSimpOnly___closed__2 = _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___closed__2);
l_Lean_Elab_Tactic_mkSimpOnly___closed__3 = _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___closed__3);
l_Lean_Elab_Tactic_mkSimpOnly___closed__4 = _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___closed__4);
l_Lean_Elab_Tactic_mkSimpOnly___closed__5 = _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___closed__5);
l_Lean_Elab_Tactic_mkSimpOnly___closed__6 = _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___closed__6);
l_Lean_Elab_Tactic_mkSimpOnly___closed__7 = _init_l_Lean_Elab_Tactic_mkSimpOnly___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_mkSimpOnly___closed__7);
l_Lean_Elab_Tactic_traceSimpCall___closed__1 = _init_l_Lean_Elab_Tactic_traceSimpCall___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_traceSimpCall___closed__1);
l_Lean_Elab_Tactic_traceSimpCall___closed__2 = _init_l_Lean_Elab_Tactic_traceSimpCall___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_traceSimpCall___closed__2);
l_Lean_Elab_Tactic_simpLocation_go___closed__1 = _init_l_Lean_Elab_Tactic_simpLocation_go___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_simpLocation_go___closed__1);
l_Lean_Elab_Tactic_simpLocation_go___closed__2 = _init_l_Lean_Elab_Tactic_simpLocation_go___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_simpLocation_go___closed__2);
l_Lean_Elab_Tactic_simpLocation_go___closed__3 = _init_l_Lean_Elab_Tactic_simpLocation_go___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_simpLocation_go___closed__3);
l_Lean_Elab_Tactic_simpLocation_go___closed__4 = _init_l_Lean_Elab_Tactic_simpLocation_go___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_simpLocation_go___closed__4);
l_Lean_Elab_Tactic_simpLocation_go___closed__5 = _init_l_Lean_Elab_Tactic_simpLocation_go___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_simpLocation_go___closed__5);
l_Lean_Elab_Tactic_simpLocation_go___closed__6 = _init_l_Lean_Elab_Tactic_simpLocation_go___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_simpLocation_go___closed__6);
l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1);
l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__1 = _init_l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__1);
l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__2 = _init_l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__2);
l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__1 = _init_l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__1();
lean_mark_persistent(l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__1);
l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__2 = _init_l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__2();
lean_mark_persistent(l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
