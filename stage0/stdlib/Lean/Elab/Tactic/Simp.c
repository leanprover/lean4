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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_traceSimpCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__2;
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
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__4;
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tactic_simp_trace;
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__4;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAll_declRange__1___closed__6;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__2;
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instBEqSimpKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__4;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2;
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
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__3;
static lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____closed__2;
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
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
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp__1___closed__5;
uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__3;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__5;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_instInhabitedSimpTheorems___spec__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__9;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_tacticToDischarge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__1;
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___closed__6;
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__4;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_1146____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_elabSimpArgs___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__1;
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Origin_key(lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__13;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_instInhabitedSimpKind;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__1;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__3___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabSimpArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__2(lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__1___closed__6;
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSimpConfigCtxCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5;
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
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1;
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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Parser_Tactic_getDSimpArgs_x3f___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__1;
static lean_object* l_Lean_Parser_Tactic_getSimpArgs_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__5;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__7;
static lean_object* l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2;
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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_576____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_LocalDecl_setBinderInfo___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8;
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
lean_object* l_Lean_Meta_Simp_Context_setSimpTheorems(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__5;
static lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__2;
static lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_withoutModifyingStateWithInfoAndMessages___at_Lean_Elab_Tactic_tacticToDischarge___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_SimpKind_noConfusion___rarg___lambda__1(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_Elab_Tactic_elabSimpArgs___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__6;
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDSimpConfigCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__5;
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f___closed__3;
uint8_t lean_is_inaccessible_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDSimpConfigCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__4___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Meta_Origin_converse(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_instBEqSimpKind;
static lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8;
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
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimp_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs_isSimproc_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_mkDischargeWrapper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticToDischarge___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkSimpContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_withoutModifyingStateWithInfoAndMessagesImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpContext___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
static lean_object* l_Lean_Elab_Tactic_elabSimpConfigCtxCore___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_simpLocation___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_simpLocation_go___closed__4;
static lean_object* l_Lean_Elab_Tactic_traceSimpCall___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(x_1);
x_12 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
if (x_12 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_inc(x_1);
x_14 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
x_16 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_erase___spec__1(x_15, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(x_2, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_19 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_9);
x_21 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Meta_SimpTheorems_erase___at_Lean_Elab_Tactic_elabSimpArgs___spec__4___lambda__2(x_2, x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_25 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpErase", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpLemma", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpStar", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpPost", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_8, x_7);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_40; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_513; 
x_21 = lean_array_uget(x_6, x_8);
x_92 = lean_ctor_get(x_9, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_9, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_95 = x_9;
} else {
 lean_dec_ref(x_9);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
lean_inc(x_21);
x_101 = l_Lean_Syntax_getKind(x_21);
x_102 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2;
x_103 = lean_name_eq(x_101, x_102);
x_513 = l_Lean_Elab_Tactic_saveState___rarg(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (x_103 == 0)
{
lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = 0;
x_104 = x_516;
x_105 = x_514;
x_106 = x_515;
goto block_512;
}
else
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_513, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_513, 1);
lean_inc(x_518);
lean_dec(x_513);
x_519 = 1;
x_104 = x_519;
x_105 = x_517;
x_106 = x_518;
goto block_512;
}
block_39:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = 1;
x_33 = lean_usize_add(x_8, x_32);
x_8 = x_33;
x_9 = x_31;
x_18 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_91:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_42, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_43, 1);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_40, 0, x_52);
x_22 = x_40;
goto block_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_44, 0);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_44);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_43, 1, x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_40, 0, x_56);
x_22 = x_40;
goto block_39;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_43, 0);
lean_inc(x_57);
lean_dec(x_43);
x_58 = lean_ctor_get(x_44, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_60 = x_44;
} else {
 lean_dec_ref(x_44);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_42, 1, x_62);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_42);
lean_ctor_set(x_40, 0, x_63);
x_22 = x_40;
goto block_39;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_42, 0);
lean_inc(x_64);
lean_dec(x_42);
x_65 = lean_ctor_get(x_43, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_66 = x_43;
} else {
 lean_dec_ref(x_43);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_44, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_44, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_69 = x_44;
} else {
 lean_dec_ref(x_44);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_40, 0, x_73);
x_22 = x_40;
goto block_39;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_74 = lean_ctor_get(x_40, 1);
lean_inc(x_74);
lean_dec(x_40);
x_75 = lean_ctor_get(x_42, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_76 = x_42;
} else {
 lean_dec_ref(x_42);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_43, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_78 = x_43;
} else {
 lean_dec_ref(x_43);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_44, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_44, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_81 = x_44;
} else {
 lean_dec_ref(x_44);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
if (lean_is_scalar(x_78)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_78;
}
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_74);
x_22 = x_86;
goto block_39;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_40);
if (x_87 == 0)
{
x_22 = x_40;
goto block_39;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_40, 0);
x_89 = lean_ctor_get(x_40, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_40);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_22 = x_90;
goto block_39;
}
}
}
block_512:
{
lean_object* x_107; lean_object* x_108; 
if (x_104 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_141 = lean_name_eq(x_101, x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_21);
x_142 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
x_143 = lean_name_eq(x_101, x_142);
lean_dec(x_101);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabSimpArgs___spec__1___rarg(x_106);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_107 = x_145;
x_108 = x_146;
goto block_139;
}
else
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_98);
lean_ctor_set(x_147, 1, x_99);
x_148 = 1;
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_94);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_106);
x_40 = x_154;
goto block_91;
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_101);
x_155 = lean_unsigned_to_nat(0u);
x_156 = l_Lean_Syntax_getArg(x_21, x_155);
x_157 = l_Lean_Syntax_isNone(x_156);
x_158 = lean_unsigned_to_nat(1u);
x_159 = l_Lean_Syntax_getArg(x_21, x_158);
x_160 = l_Lean_Syntax_isNone(x_159);
lean_dec(x_159);
x_161 = lean_unsigned_to_nat(2u);
x_162 = l_Lean_Syntax_getArg(x_21, x_161);
if (x_157 == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; 
x_486 = l_Lean_Syntax_getArg(x_156, x_155);
lean_dec(x_156);
x_487 = l_Lean_Syntax_getKind(x_486);
x_488 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8;
x_489 = lean_name_eq(x_487, x_488);
lean_dec(x_487);
x_163 = x_489;
goto block_485;
}
else
{
uint8_t x_490; 
lean_dec(x_156);
x_490 = 1;
x_163 = x_490;
goto block_485;
}
block_485:
{
uint8_t x_164; 
if (x_160 == 0)
{
uint8_t x_483; 
x_483 = 1;
x_164 = x_483;
goto block_482;
}
else
{
uint8_t x_484; 
x_484 = 0;
x_164 = x_484;
goto block_482;
}
block_482:
{
lean_object* x_165; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_162);
x_165 = l_Lean_Elab_Tactic_elabSimpArgs_resolveSimpIdTheorem_x3f(x_162, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_106);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
switch (lean_obj_tag(x_166)) {
case 0:
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_165);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_ctor_get(x_165, 0);
lean_dec(x_169);
x_170 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_17, x_168);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 1);
lean_ctor_set_tag(x_170, 2);
lean_ctor_set(x_170, 1, x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_98);
x_173 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_98, x_170, x_162, x_163, x_164, x_12, x_13, x_14, x_15, x_16, x_17, x_172);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_173, 0);
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_175);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_96);
lean_ctor_set(x_176, 1, x_165);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_94);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_box(0);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_173, 0, x_179);
x_40 = x_173;
goto block_91;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_180 = lean_ctor_get(x_173, 0);
x_181 = lean_ctor_get(x_173, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_173);
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_96);
lean_ctor_set(x_182, 1, x_165);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_94);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
x_40 = x_186;
goto block_91;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_free_object(x_165);
x_187 = lean_ctor_get(x_173, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_173, 1);
lean_inc(x_188);
lean_dec(x_173);
x_107 = x_187;
x_108 = x_188;
goto block_139;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_170, 0);
x_190 = lean_ctor_get(x_170, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_170);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_98);
x_192 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_98, x_191, x_162, x_163, x_164, x_12, x_13, x_14, x_15, x_16, x_17, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_96);
lean_ctor_set(x_196, 1, x_165);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_94);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_194);
x_40 = x_200;
goto block_91;
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_free_object(x_165);
x_201 = lean_ctor_get(x_192, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_192, 1);
lean_inc(x_202);
lean_dec(x_192);
x_107 = x_201;
x_108 = x_202;
goto block_139;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_165, 1);
lean_inc(x_203);
lean_dec(x_165);
x_204 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_17, x_203);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(2, 2, 0);
} else {
 x_208 = x_207;
 lean_ctor_set_tag(x_208, 2);
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_98);
x_209 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addSimpTheorem(x_98, x_208, x_162, x_163, x_164, x_12, x_13, x_14, x_15, x_16, x_17, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_99);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_96);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_94);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_box(0);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
if (lean_is_scalar(x_212)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_212;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_211);
x_40 = x_218;
goto block_91;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_209, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_209, 1);
lean_inc(x_220);
lean_dec(x_209);
x_107 = x_219;
x_108 = x_220;
goto block_139;
}
}
}
case 1:
{
uint8_t x_221; 
lean_dec(x_162);
x_221 = !lean_is_exclusive(x_165);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_165, 1);
x_223 = lean_ctor_get(x_165, 0);
lean_dec(x_223);
x_224 = lean_ctor_get(x_166, 0);
lean_inc(x_224);
lean_dec(x_166);
x_225 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_17, x_222);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 1);
lean_ctor_set_tag(x_225, 2);
lean_ctor_set(x_225, 1, x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_98);
x_228 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_98, x_225, x_224, x_163, x_164, x_3, x_14, x_15, x_16, x_17, x_227);
if (lean_obj_tag(x_228) == 0)
{
uint8_t x_229; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_ctor_get(x_228, 0);
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_230);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_96);
lean_ctor_set(x_231, 1, x_165);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_94);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
lean_ctor_set(x_228, 0, x_234);
x_40 = x_228;
goto block_91;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_235 = lean_ctor_get(x_228, 0);
x_236 = lean_ctor_get(x_228, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_228);
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_96);
lean_ctor_set(x_237, 1, x_165);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_94);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_box(0);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_236);
x_40 = x_241;
goto block_91;
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_free_object(x_165);
x_242 = lean_ctor_get(x_228, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_228, 1);
lean_inc(x_243);
lean_dec(x_228);
x_107 = x_242;
x_108 = x_243;
goto block_139;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_225, 0);
x_245 = lean_ctor_get(x_225, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_225);
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_98);
x_247 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_98, x_246, x_224, x_163, x_164, x_3, x_14, x_15, x_16, x_17, x_245);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_248);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_96);
lean_ctor_set(x_251, 1, x_165);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_94);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_250;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_249);
x_40 = x_255;
goto block_91;
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_free_object(x_165);
x_256 = lean_ctor_get(x_247, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_247, 1);
lean_inc(x_257);
lean_dec(x_247);
x_107 = x_256;
x_108 = x_257;
goto block_139;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_258 = lean_ctor_get(x_165, 1);
lean_inc(x_258);
lean_dec(x_165);
x_259 = lean_ctor_get(x_166, 0);
lean_inc(x_259);
lean_dec(x_166);
x_260 = l_Lean_mkFreshId___at_Lean_Elab_Tactic_elabSimpArgs___spec__2___rarg(x_17, x_258);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_263 = x_260;
} else {
 lean_dec_ref(x_260);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(2, 2, 0);
} else {
 x_264 = x_263;
 lean_ctor_set_tag(x_264, 2);
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_98);
x_265 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem(x_98, x_264, x_259, x_163, x_164, x_3, x_14, x_15, x_16, x_17, x_262);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_268 = x_265;
} else {
 lean_dec_ref(x_265);
 x_268 = lean_box(0);
}
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_99);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_96);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_94);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
if (lean_is_scalar(x_268)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_268;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_267);
x_40 = x_274;
goto block_91;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_265, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_265, 1);
lean_inc(x_276);
lean_dec(x_265);
x_107 = x_275;
x_108 = x_276;
goto block_139;
}
}
}
case 2:
{
uint8_t x_277; 
lean_dec(x_162);
lean_dec(x_21);
x_277 = !lean_is_exclusive(x_165);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_165, 1);
x_279 = lean_ctor_get(x_165, 0);
lean_dec(x_279);
x_280 = lean_ctor_get(x_166, 0);
lean_inc(x_280);
lean_dec(x_166);
lean_inc(x_94);
x_281 = l_Lean_Meta_Simp_SimprocsArray_add(x_94, x_280, x_163, x_16, x_17, x_278);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_281, 0);
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_98);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_96);
lean_ctor_set(x_284, 1, x_165);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_box(0);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_285);
lean_ctor_set(x_281, 0, x_287);
x_40 = x_281;
goto block_91;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_281, 0);
x_289 = lean_ctor_get(x_281, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_281);
lean_ctor_set(x_165, 1, x_99);
lean_ctor_set(x_165, 0, x_98);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_96);
lean_ctor_set(x_290, 1, x_165);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_box(0);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_289);
x_40 = x_294;
goto block_91;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_free_object(x_165);
x_295 = lean_ctor_get(x_281, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_281, 1);
lean_inc(x_296);
lean_dec(x_281);
x_107 = x_295;
x_108 = x_296;
goto block_139;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_165, 1);
lean_inc(x_297);
lean_dec(x_165);
x_298 = lean_ctor_get(x_166, 0);
lean_inc(x_298);
lean_dec(x_166);
lean_inc(x_94);
x_299 = l_Lean_Meta_Simp_SimprocsArray_add(x_94, x_298, x_163, x_16, x_17, x_297);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_94);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_98);
lean_ctor_set(x_303, 1, x_99);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_96);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_300);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_box(0);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
if (lean_is_scalar(x_302)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_302;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_301);
x_40 = x_308;
goto block_91;
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_299, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_299, 1);
lean_inc(x_310);
lean_dec(x_299);
x_107 = x_309;
x_108 = x_310;
goto block_139;
}
}
}
default: 
{
lean_object* x_311; 
lean_dec(x_162);
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_21);
x_311 = lean_ctor_get(x_166, 0);
lean_inc(x_311);
if (lean_obj_tag(x_311) == 0)
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_166);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_313 = lean_ctor_get(x_166, 1);
x_314 = lean_ctor_get(x_166, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_165);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_316 = lean_ctor_get(x_165, 1);
x_317 = lean_ctor_get(x_165, 0);
lean_dec(x_317);
x_318 = lean_ctor_get(x_313, 0);
lean_inc(x_318);
lean_dec(x_313);
x_319 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_318, x_16, x_17, x_316);
lean_dec(x_318);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_321 = lean_ctor_get(x_319, 0);
x_322 = lean_array_push(x_94, x_321);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_99);
lean_ctor_set(x_166, 0, x_98);
lean_ctor_set(x_165, 1, x_166);
lean_ctor_set(x_165, 0, x_96);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_165);
x_324 = lean_box(0);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
lean_ctor_set(x_319, 0, x_325);
x_40 = x_319;
goto block_91;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_326 = lean_ctor_get(x_319, 0);
x_327 = lean_ctor_get(x_319, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_319);
x_328 = lean_array_push(x_94, x_326);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_99);
lean_ctor_set(x_166, 0, x_98);
lean_ctor_set(x_165, 1, x_166);
lean_ctor_set(x_165, 0, x_96);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_165);
x_330 = lean_box(0);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_329);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_327);
x_40 = x_332;
goto block_91;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_333 = lean_ctor_get(x_165, 1);
lean_inc(x_333);
lean_dec(x_165);
x_334 = lean_ctor_get(x_313, 0);
lean_inc(x_334);
lean_dec(x_313);
x_335 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_334, x_16, x_17, x_333);
lean_dec(x_334);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = lean_array_push(x_94, x_336);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_99);
lean_ctor_set(x_166, 0, x_98);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_96);
lean_ctor_set(x_340, 1, x_166);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_box(0);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
if (lean_is_scalar(x_338)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_338;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_337);
x_40 = x_344;
goto block_91;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_345 = lean_ctor_get(x_166, 1);
lean_inc(x_345);
lean_dec(x_166);
x_346 = lean_ctor_get(x_165, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_347 = x_165;
} else {
 lean_dec_ref(x_165);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
lean_dec(x_345);
x_349 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_348, x_16, x_17, x_346);
lean_dec(x_348);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_352 = x_349;
} else {
 lean_dec_ref(x_349);
 x_352 = lean_box(0);
}
x_353 = lean_array_push(x_94, x_350);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_98);
lean_ctor_set(x_354, 1, x_99);
if (lean_is_scalar(x_347)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_347;
}
lean_ctor_set(x_355, 0, x_96);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_box(0);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
if (lean_is_scalar(x_352)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_352;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_351);
x_40 = x_359;
goto block_91;
}
}
else
{
uint8_t x_360; 
x_360 = !lean_is_exclusive(x_166);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_166, 1);
x_362 = lean_ctor_get(x_166, 0);
lean_dec(x_362);
if (lean_obj_tag(x_361) == 0)
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_165);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_364 = lean_ctor_get(x_165, 1);
x_365 = lean_ctor_get(x_165, 0);
lean_dec(x_365);
x_366 = lean_ctor_get(x_311, 0);
lean_inc(x_366);
lean_dec(x_311);
x_367 = l_Lean_Meta_SimpExtension_getTheorems(x_366, x_16, x_17, x_364);
lean_dec(x_366);
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = lean_array_push(x_99, x_369);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_370);
lean_ctor_set(x_166, 0, x_98);
lean_ctor_set(x_165, 1, x_166);
lean_ctor_set(x_165, 0, x_96);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_94);
lean_ctor_set(x_371, 1, x_165);
x_372 = lean_box(0);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_371);
lean_ctor_set(x_367, 0, x_373);
x_40 = x_367;
goto block_91;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_367, 0);
x_375 = lean_ctor_get(x_367, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_367);
x_376 = lean_array_push(x_99, x_374);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_376);
lean_ctor_set(x_166, 0, x_98);
lean_ctor_set(x_165, 1, x_166);
lean_ctor_set(x_165, 0, x_96);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_94);
lean_ctor_set(x_377, 1, x_165);
x_378 = lean_box(0);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_375);
x_40 = x_380;
goto block_91;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_381 = lean_ctor_get(x_165, 1);
lean_inc(x_381);
lean_dec(x_165);
x_382 = lean_ctor_get(x_311, 0);
lean_inc(x_382);
lean_dec(x_311);
x_383 = l_Lean_Meta_SimpExtension_getTheorems(x_382, x_16, x_17, x_381);
lean_dec(x_382);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_386 = x_383;
} else {
 lean_dec_ref(x_383);
 x_386 = lean_box(0);
}
x_387 = lean_array_push(x_99, x_384);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_387);
lean_ctor_set(x_166, 0, x_98);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_96);
lean_ctor_set(x_388, 1, x_166);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_94);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_box(0);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_389);
if (lean_is_scalar(x_386)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_386;
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_385);
x_40 = x_392;
goto block_91;
}
}
else
{
uint8_t x_393; 
x_393 = !lean_is_exclusive(x_165);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_394 = lean_ctor_get(x_165, 1);
x_395 = lean_ctor_get(x_165, 0);
lean_dec(x_395);
x_396 = lean_ctor_get(x_311, 0);
lean_inc(x_396);
lean_dec(x_311);
x_397 = lean_ctor_get(x_361, 0);
lean_inc(x_397);
lean_dec(x_361);
x_398 = l_Lean_Meta_SimpExtension_getTheorems(x_396, x_16, x_17, x_394);
lean_dec(x_396);
x_399 = !lean_is_exclusive(x_398);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_400 = lean_ctor_get(x_398, 0);
x_401 = lean_ctor_get(x_398, 1);
x_402 = lean_array_push(x_99, x_400);
x_403 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_397, x_16, x_17, x_401);
lean_dec(x_397);
x_404 = !lean_is_exclusive(x_403);
if (x_404 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_403, 0);
x_406 = lean_array_push(x_94, x_405);
lean_ctor_set(x_398, 1, x_402);
lean_ctor_set(x_398, 0, x_98);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_398);
lean_ctor_set(x_166, 0, x_96);
lean_ctor_set(x_165, 1, x_166);
lean_ctor_set(x_165, 0, x_406);
x_407 = lean_box(0);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_165);
lean_ctor_set(x_403, 0, x_408);
x_40 = x_403;
goto block_91;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_409 = lean_ctor_get(x_403, 0);
x_410 = lean_ctor_get(x_403, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_403);
x_411 = lean_array_push(x_94, x_409);
lean_ctor_set(x_398, 1, x_402);
lean_ctor_set(x_398, 0, x_98);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_398);
lean_ctor_set(x_166, 0, x_96);
lean_ctor_set(x_165, 1, x_166);
lean_ctor_set(x_165, 0, x_411);
x_412 = lean_box(0);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_165);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_410);
x_40 = x_414;
goto block_91;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_415 = lean_ctor_get(x_398, 0);
x_416 = lean_ctor_get(x_398, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_398);
x_417 = lean_array_push(x_99, x_415);
x_418 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_397, x_16, x_17, x_416);
lean_dec(x_397);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_421 = x_418;
} else {
 lean_dec_ref(x_418);
 x_421 = lean_box(0);
}
x_422 = lean_array_push(x_94, x_419);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_98);
lean_ctor_set(x_423, 1, x_417);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_423);
lean_ctor_set(x_166, 0, x_96);
lean_ctor_set(x_165, 1, x_166);
lean_ctor_set(x_165, 0, x_422);
x_424 = lean_box(0);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_165);
if (lean_is_scalar(x_421)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_421;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_420);
x_40 = x_426;
goto block_91;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_427 = lean_ctor_get(x_165, 1);
lean_inc(x_427);
lean_dec(x_165);
x_428 = lean_ctor_get(x_311, 0);
lean_inc(x_428);
lean_dec(x_311);
x_429 = lean_ctor_get(x_361, 0);
lean_inc(x_429);
lean_dec(x_361);
x_430 = l_Lean_Meta_SimpExtension_getTheorems(x_428, x_16, x_17, x_427);
lean_dec(x_428);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_433 = x_430;
} else {
 lean_dec_ref(x_430);
 x_433 = lean_box(0);
}
x_434 = lean_array_push(x_99, x_431);
x_435 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_429, x_16, x_17, x_432);
lean_dec(x_429);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_438 = x_435;
} else {
 lean_dec_ref(x_435);
 x_438 = lean_box(0);
}
x_439 = lean_array_push(x_94, x_436);
if (lean_is_scalar(x_433)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_433;
}
lean_ctor_set(x_440, 0, x_98);
lean_ctor_set(x_440, 1, x_434);
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_440);
lean_ctor_set(x_166, 0, x_96);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_166);
x_442 = lean_box(0);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
if (lean_is_scalar(x_438)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_438;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_437);
x_40 = x_444;
goto block_91;
}
}
}
else
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_166, 1);
lean_inc(x_445);
lean_dec(x_166);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_446 = lean_ctor_get(x_165, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_447 = x_165;
} else {
 lean_dec_ref(x_165);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_311, 0);
lean_inc(x_448);
lean_dec(x_311);
x_449 = l_Lean_Meta_SimpExtension_getTheorems(x_448, x_16, x_17, x_446);
lean_dec(x_448);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_452 = x_449;
} else {
 lean_dec_ref(x_449);
 x_452 = lean_box(0);
}
x_453 = lean_array_push(x_99, x_450);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_98);
lean_ctor_set(x_454, 1, x_453);
if (lean_is_scalar(x_447)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_447;
}
lean_ctor_set(x_455, 0, x_96);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_94);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_box(0);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_456);
if (lean_is_scalar(x_452)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_452;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_451);
x_40 = x_459;
goto block_91;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_460 = lean_ctor_get(x_165, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_461 = x_165;
} else {
 lean_dec_ref(x_165);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_311, 0);
lean_inc(x_462);
lean_dec(x_311);
x_463 = lean_ctor_get(x_445, 0);
lean_inc(x_463);
lean_dec(x_445);
x_464 = l_Lean_Meta_SimpExtension_getTheorems(x_462, x_16, x_17, x_460);
lean_dec(x_462);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_467 = x_464;
} else {
 lean_dec_ref(x_464);
 x_467 = lean_box(0);
}
x_468 = lean_array_push(x_99, x_465);
x_469 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_463, x_16, x_17, x_466);
lean_dec(x_463);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
x_473 = lean_array_push(x_94, x_470);
if (lean_is_scalar(x_467)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_467;
}
lean_ctor_set(x_474, 0, x_98);
lean_ctor_set(x_474, 1, x_468);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_96);
lean_ctor_set(x_475, 1, x_474);
if (lean_is_scalar(x_461)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_461;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_475);
x_477 = lean_box(0);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_476);
if (lean_is_scalar(x_472)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_472;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_471);
x_40 = x_479;
goto block_91;
}
}
}
}
}
}
else
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_162);
lean_dec(x_21);
x_480 = lean_ctor_get(x_165, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_165, 1);
lean_inc(x_481);
lean_dec(x_165);
x_107 = x_480;
x_108 = x_481;
goto block_139;
}
}
}
}
}
else
{
lean_dec(x_101);
if (x_2 == 0)
{
uint8_t x_491; 
x_491 = lean_unbox(x_96);
if (x_491 == 0)
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_98);
lean_inc(x_94);
lean_inc(x_96);
lean_inc(x_99);
x_493 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_21, x_99, x_96, x_1, x_94, x_98, x_492, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_106);
lean_dec(x_21);
if (lean_obj_tag(x_493) == 0)
{
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_40 = x_493;
goto block_91;
}
else
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_107 = x_494;
x_108 = x_495;
goto block_139;
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_496 = lean_unsigned_to_nat(1u);
x_497 = l_Lean_Syntax_getArg(x_21, x_496);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_12);
x_498 = l_Lean_Elab_Term_isLocalIdent_x3f(x_497, x_12, x_13, x_14, x_15, x_16, x_17, x_106);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_98);
lean_inc(x_94);
lean_inc(x_96);
lean_inc(x_99);
x_501 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_21, x_99, x_96, x_1, x_94, x_98, x_499, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_500);
lean_dec(x_21);
if (lean_obj_tag(x_501) == 0)
{
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_40 = x_501;
goto block_91;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_107 = x_502;
x_108 = x_503;
goto block_139;
}
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_504 = lean_unsigned_to_nat(1u);
x_505 = l_Lean_Syntax_getArg(x_21, x_504);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_12);
x_506 = l_Lean_Elab_Term_isLocalIdent_x3f(x_505, x_12, x_13, x_14, x_15, x_16, x_17, x_106);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_98);
lean_inc(x_94);
lean_inc(x_96);
lean_inc(x_99);
x_509 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_21, x_99, x_96, x_1, x_94, x_98, x_507, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_508);
lean_dec(x_21);
if (lean_obj_tag(x_509) == 0)
{
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_40 = x_509;
goto block_91;
}
else
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec(x_509);
x_107 = x_510;
x_108 = x_511;
goto block_139;
}
}
}
block_139:
{
uint8_t x_109; 
x_109 = l_Lean_Exception_isInterrupt(x_107);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_Lean_Exception_isRuntime(x_107);
if (x_110 == 0)
{
uint8_t x_111; lean_object* x_112; uint8_t x_113; 
x_111 = 0;
x_112 = l_Lean_Elab_Tactic_SavedState_restore(x_105, x_111, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_108);
x_113 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_113 == 0)
{
uint8_t x_114; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
lean_ctor_set_tag(x_112, 1);
lean_ctor_set(x_112, 0, x_107);
x_40 = x_112;
goto block_91;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_116);
x_40 = x_117;
goto block_91;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_dec(x_112);
lean_inc(x_16);
x_119 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_107, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_119, 0);
if (lean_is_scalar(x_100)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_100;
}
lean_ctor_set(x_122, 0, x_98);
lean_ctor_set(x_122, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_97;
}
lean_ctor_set(x_123, 0, x_96);
lean_ctor_set(x_123, 1, x_122);
if (lean_is_scalar(x_95)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_95;
}
lean_ctor_set(x_124, 0, x_94);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_119, 0, x_125);
x_40 = x_119;
goto block_91;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_119, 0);
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_119);
if (lean_is_scalar(x_100)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_100;
}
lean_ctor_set(x_128, 0, x_98);
lean_ctor_set(x_128, 1, x_99);
if (lean_is_scalar(x_97)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_97;
}
lean_ctor_set(x_129, 0, x_96);
lean_ctor_set(x_129, 1, x_128);
if (lean_is_scalar(x_95)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_95;
}
lean_ctor_set(x_130, 0, x_94);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_127);
x_40 = x_132;
goto block_91;
}
}
else
{
uint8_t x_133; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_133 = !lean_is_exclusive(x_119);
if (x_133 == 0)
{
x_40 = x_119;
goto block_91;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_119, 0);
x_135 = lean_ctor_get(x_119, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_119);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_40 = x_136;
goto block_91;
}
}
}
}
else
{
lean_object* x_137; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_107);
lean_ctor_set(x_137, 1, x_108);
x_40 = x_137;
goto block_91;
}
}
else
{
lean_object* x_138; 
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_107);
lean_ctor_set(x_138, 1, x_108);
x_40 = x_138;
goto block_91;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(x_1, x_2, x_3, x_4, x_5, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_set(x_27, x_28, x_26);
x_30 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_1, x_29);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
x_32 = lean_unbox(x_25);
lean_dec(x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_32);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_set(x_37, x_38, x_36);
x_40 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_1, x_39);
x_41 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
x_42 = lean_unbox(x_35);
lean_dec(x_35);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_42);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; uint8_t x_25; lean_object* x_26; 
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
x_23 = lean_box(0);
x_24 = lean_array_size(x_22);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Meta_instInhabitedSimpTheorems;
x_42 = l_outOfBounds___rarg(x_41);
x_26 = x_42;
goto block_40;
}
else
{
lean_object* x_43; 
x_43 = lean_array_fget(x_16, x_18);
x_26 = x_43;
goto block_40;
}
block_40:
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(x_4);
x_33 = lean_box(x_5);
x_34 = lean_box_usize(x_24);
x_35 = l_Lean_Elab_Tactic_elabSimpArgs___boxed__const__1;
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabSimpArgs___lambda__1___boxed), 17, 8);
lean_closure_set(x_36, 0, x_2);
lean_closure_set(x_36, 1, x_32);
lean_closure_set(x_36, 2, x_33);
lean_closure_set(x_36, 3, x_22);
lean_closure_set(x_36, 4, x_23);
lean_closure_set(x_36, 5, x_34);
lean_closure_set(x_36, 6, x_35);
lean_closure_set(x_36, 7, x_31);
if (x_25 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_elabSimpArgs___spec__7(x_37, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Elab_Tactic_withMainContext___rarg(x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_39;
}
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_14);
return x_46;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_unbox(x_2);
lean_dec(x_2);
x_20 = lean_unbox(x_3);
lean_dec(x_3);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6(x_1, x_19, x_20, x_4, x_5, x_6, x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabSimpArgs___lambda__1___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = l_Lean_Elab_Tactic_elabSimpArgs___lambda__1(x_1, x_18, x_19, x_4, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_array_uget(x_3, x_5);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Meta_SimpTheoremsArray_isErased(x_6, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_11);
x_21 = l_Lean_FVarId_getDecl(x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_toExpr(x_22);
lean_dec(x_22);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_6, x_19, x_24, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_6 = x_26;
x_15 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
size_t x_39; size_t x_40; 
lean_dec(x_19);
lean_dec(x_18);
x_39 = 1;
x_40 = lean_usize_add(x_5, x_39);
x_5 = x_40;
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_3);
x_27 = lean_array_mk(x_17);
x_28 = l_Lean_Meta_Simp_mkContext(x_24, x_27, x_19, x_12, x_13, x_14, x_15, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_unsigned_to_nat(4u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 0, x_7);
x_34 = lean_array_mk(x_28);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_35 = l_Lean_Elab_Tactic_elabSimpArgs(x_33, x_30, x_34, x_4, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_31);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_5);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
else
{
if (x_6 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_ctor_get(x_36, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_dec(x_36);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_52 = l_Lean_Meta_getPropHyps(x_12, x_13, x_14, x_15, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = lean_array_size(x_53);
x_57 = 0;
x_58 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_53, x_55, x_53, x_56, x_57, x_51, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_53);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_49, x_60);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
lean_ctor_set(x_62, 2, x_5);
lean_ctor_set(x_58, 0, x_62);
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_49, x_63);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
lean_ctor_set(x_66, 2, x_5);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_58);
if (x_68 == 0)
{
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_72 = !lean_is_exclusive(x_52);
if (x_72 == 0)
{
return x_52;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_52, 0);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_52);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_35);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_35, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_36, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_36, 1);
lean_inc(x_79);
lean_dec(x_36);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_5);
lean_ctor_set(x_35, 0, x_80);
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_dec(x_35);
x_82 = lean_ctor_get(x_36, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_36, 1);
lean_inc(x_83);
lean_dec(x_36);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_5);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_86 = !lean_is_exclusive(x_35);
if (x_86 == 0)
{
return x_35;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_35, 0);
x_88 = lean_ctor_get(x_35, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_35);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_28, 0);
x_91 = lean_ctor_get(x_28, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_28);
x_92 = lean_unsigned_to_nat(4u);
x_93 = l_Lean_Syntax_getArg(x_1, x_92);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_7);
lean_ctor_set(x_94, 1, x_26);
x_95 = lean_array_mk(x_94);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_96 = l_Lean_Elab_Tactic_elabSimpArgs(x_93, x_90, x_95, x_4, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_91);
lean_dec(x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_97, sizeof(void*)*2);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_97, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_dec(x_97);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_5);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
return x_104;
}
else
{
if (x_6 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_96, 1);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_ctor_get(x_97, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_97, 1);
lean_inc(x_107);
lean_dec(x_97);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_109 = l_Lean_Meta_getPropHyps(x_12, x_13, x_14, x_15, x_105);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_box(0);
x_113 = lean_array_size(x_110);
x_114 = 0;
x_115 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_110, x_112, x_110, x_113, x_114, x_108, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_111);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_110);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_106, x_116);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_107);
lean_ctor_set(x_120, 2, x_5);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_5);
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_124 = x_115;
} else {
 lean_dec_ref(x_115);
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
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_126 = lean_ctor_get(x_109, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_109, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_128 = x_109;
} else {
 lean_dec_ref(x_109);
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
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_130 = lean_ctor_get(x_96, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_131 = x_96;
} else {
 lean_dec_ref(x_96);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_97, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_97, 1);
lean_inc(x_133);
lean_dec(x_97);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_5);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_136 = lean_ctor_get(x_96, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_96, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_138 = x_96;
} else {
 lean_dec_ref(x_96);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
uint8_t x_140; 
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
x_140 = !lean_is_exclusive(x_23);
if (x_140 == 0)
{
return x_23;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_23, 0);
x_142 = lean_ctor_get(x_23, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_23);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_17, 0);
x_145 = lean_ctor_get(x_17, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_17);
x_146 = lean_unsigned_to_nat(1u);
x_147 = l_Lean_Syntax_getArg(x_1, x_146);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_148 = l_Lean_Elab_Tactic_elabSimpConfig(x_147, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_3);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_array_mk(x_152);
x_154 = l_Lean_Meta_Simp_mkContext(x_149, x_153, x_144, x_12, x_13, x_14, x_15, x_150);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_unsigned_to_nat(4u);
x_159 = l_Lean_Syntax_getArg(x_1, x_158);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_157;
 lean_ctor_set_tag(x_160, 1);
}
lean_ctor_set(x_160, 0, x_7);
lean_ctor_set(x_160, 1, x_151);
x_161 = lean_array_mk(x_160);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_162 = l_Lean_Elab_Tactic_elabSimpArgs(x_159, x_155, x_161, x_4, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_156);
lean_dec(x_159);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_163, sizeof(void*)*2);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_5);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_166;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_165);
return x_170;
}
else
{
if (x_6 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_162, 1);
lean_inc(x_171);
lean_dec(x_162);
x_172 = lean_ctor_get(x_163, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
lean_dec(x_163);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_175 = l_Lean_Meta_getPropHyps(x_12, x_13, x_14, x_15, x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; size_t x_179; size_t x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_box(0);
x_179 = lean_array_size(x_176);
x_180 = 0;
x_181 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_176, x_178, x_176, x_179, x_180, x_174, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_177);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_176);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_184 = x_181;
} else {
 lean_dec_ref(x_181);
 x_184 = lean_box(0);
}
x_185 = l_Lean_Meta_Simp_Context_setSimpTheorems(x_172, x_182);
x_186 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_173);
lean_ctor_set(x_186, 2, x_5);
if (lean_is_scalar(x_184)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_184;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_183);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_5);
x_188 = lean_ctor_get(x_181, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_181, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_190 = x_181;
} else {
 lean_dec_ref(x_181);
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
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_192 = lean_ctor_get(x_175, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_175, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_194 = x_175;
} else {
 lean_dec_ref(x_175);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_196 = lean_ctor_get(x_162, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_197 = x_162;
} else {
 lean_dec_ref(x_162);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_163, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_163, 1);
lean_inc(x_199);
lean_dec(x_163);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_5);
if (lean_is_scalar(x_197)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_197;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_196);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_202 = lean_ctor_get(x_162, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_162, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_204 = x_162;
} else {
 lean_dec_ref(x_162);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_144);
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
x_206 = lean_ctor_get(x_148, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_148, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_208 = x_148;
} else {
 lean_dec_ref(x_148);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpContext___spec__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
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
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1;
x_3 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("When tracing is enabled, calls to `simp` or `dsimp` will print an equivalent `simp only` call.", 94, 94);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Elab_Tactic_elabSimpConfigCore___lambda__1___closed__5;
x_3 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__1;
x_5 = l_Lean_Elab_Tactic_tacticToDischarge___lambda__3___closed__1;
x_6 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__2;
x_7 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__3;
x_3 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__5;
x_4 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__7;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l_Lean_Name_appendCore(x_16, x_18);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_19);
x_20 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(x_19, x_9, x_10, x_11, x_12, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_4);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_6, 0, x_4);
{
lean_object* _tmp_5 = x_17;
lean_object* _tmp_6 = x_6;
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_12 = x_22;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_6);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_dec(x_31);
x_32 = lean_name_eq(x_30, x_1);
lean_dec(x_30);
if (x_32 == 0)
{
lean_free_object(x_20);
lean_inc(x_4);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 0, x_4);
x_6 = x_17;
x_7 = x_24;
x_8 = lean_box(0);
x_13 = x_27;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_4);
lean_inc(x_19);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_19);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 0, x_35);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_name_eq(x_36, x_1);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_free_object(x_20);
lean_inc(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_19);
x_6 = x_17;
x_7 = x_38;
x_8 = lean_box(0);
x_13 = x_27;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_4);
lean_inc(x_19);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_19);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_20, 0, x_42);
return x_20;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_dec(x_20);
x_44 = lean_ctor_get(x_24, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_45 = x_24;
} else {
 lean_dec_ref(x_24);
 x_45 = lean_box(0);
}
x_46 = lean_name_eq(x_44, x_1);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_inc(x_4);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_19);
x_6 = x_17;
x_7 = x_47;
x_8 = lean_box(0);
x_13 = x_43;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_4);
lean_inc(x_19);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_19);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_19);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_25, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_dec(x_20);
lean_inc(x_4);
lean_ctor_set_tag(x_25, 0);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 0, x_4);
x_6 = x_17;
x_7 = x_25;
x_8 = lean_box(0);
x_13 = x_56;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_25);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_dec(x_20);
lean_inc(x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_19);
x_6 = x_17;
x_7 = x_59;
x_8 = lean_box(0);
x_13 = x_58;
goto _start;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_6, 0);
x_62 = lean_ctor_get(x_6, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_6);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_dec(x_7);
x_64 = l_Lean_Name_appendCore(x_61, x_63);
lean_dec(x_61);
lean_inc(x_11);
lean_inc(x_64);
x_65 = l_Lean_resolveGlobalName___at_Lean_Elab_Tactic_mkSimpOnly___spec__4(x_64, x_9, x_10, x_11, x_12, x_13);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_4);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_64);
x_6 = x_62;
x_7 = x_68;
x_8 = lean_box(0);
x_13 = x_67;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
x_76 = lean_name_eq(x_74, x_1);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_73);
lean_inc(x_4);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_64);
x_6 = x_62;
x_7 = x_77;
x_8 = lean_box(0);
x_13 = x_72;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_62);
lean_dec(x_11);
lean_dec(x_4);
lean_inc(x_64);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_64);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_72);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_70);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_83 = x_71;
} else {
 lean_dec_ref(x_71);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_dec(x_65);
lean_inc(x_4);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
 lean_ctor_set_tag(x_85, 0);
}
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_64);
x_6 = x_62;
x_7 = x_85;
x_8 = lean_box(0);
x_13 = x_84;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_Name_componentsRev(x_1);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3___lambda__2___closed__1;
lean_inc(x_9);
x_13 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(x_2, x_9, x_10, x_11, x_9, x_9, x_12, lean_box(0), x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
lean_inc(x_11);
x_17 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkSimpOnly___spec__3(x_1, x_16, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
lean_inc(x_4);
{
size_t _tmp_6 = x_21;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_12 = x_19;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_17, 0, x_31);
return x_17;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_34 = x_18;
} else {
 lean_dec_ref(x_18);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_17 = lean_box(0);
x_18 = lean_array_size(x_16);
x_19 = 0;
x_20 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkSimpOnly___spec__2___lambda__1___closed__1;
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(x_1, x_16, x_17, x_20, x_16, x_18, x_19, x_20, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4;
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
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4;
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpPre", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Simp___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_tacticToDischarge___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticToDischarge___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("↓", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("patternIgnore", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7;
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("←", 3, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_9, x_8);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_7, x_9);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_88; uint8_t x_272; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_29 = x_10;
} else {
 lean_dec_ref(x_10);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*1 + 1);
lean_dec(x_18);
lean_inc(x_4);
x_272 = l_Lean_Environment_contains(x_4, x_30);
if (x_272 == 0)
{
lean_object* x_273; 
x_273 = lean_box(0);
x_33 = x_273;
goto block_87;
}
else
{
if (x_32 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__4;
lean_inc(x_2);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_2);
x_276 = l_Lean_Elab_Tactic_simpOnlyBuiltins___closed__2;
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_30, x_277);
lean_dec(x_277);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = l_Lean_Meta_Match_isMatchEqnTheorem(x_4, x_30);
if (x_279 == 0)
{
lean_object* x_280; 
lean_dec(x_29);
x_280 = lean_box(0);
x_88 = x_280;
goto block_271;
}
else
{
lean_object* x_281; 
x_281 = lean_box(0);
x_33 = x_281;
goto block_87;
}
}
else
{
lean_object* x_282; 
x_282 = lean_box(0);
x_33 = x_282;
goto block_87;
}
}
else
{
uint8_t x_283; 
x_283 = l_Lean_Meta_Match_isMatchEqnTheorem(x_4, x_30);
if (x_283 == 0)
{
lean_object* x_284; 
lean_dec(x_29);
x_284 = lean_box(0);
x_88 = x_284;
goto block_271;
}
else
{
lean_object* x_285; 
x_285 = lean_box(0);
x_33 = x_285;
goto block_87;
}
}
}
block_87:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_33);
x_34 = l_Lean_Meta_Simp_isBuiltinSimproc(x_30, x_13, x_14, x_15);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
if (lean_is_scalar(x_29)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_29;
}
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_28);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_34, 0, x_40);
x_19 = x_34;
goto block_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
if (lean_is_scalar(x_29)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_29;
}
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_28);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
x_19 = x_44;
goto block_26;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_29);
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_mk_syntax_ident(x_30);
if (x_31 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_13, 5);
lean_inc(x_47);
x_48 = 0;
x_49 = l_Lean_SourceInfo_fromRef(x_47, x_48);
lean_dec(x_47);
x_50 = lean_st_ref_get(x_14, x_45);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_49);
lean_ctor_set_tag(x_50, 2);
lean_ctor_set(x_50, 1, x_54);
lean_ctor_set(x_50, 0, x_49);
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_49);
x_56 = l_Lean_Syntax_node1(x_49, x_55, x_50);
x_57 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_49);
x_58 = l_Lean_Syntax_node1(x_49, x_57, x_56);
x_59 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_49);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_62 = l_Lean_Syntax_node3(x_49, x_61, x_58, x_60, x_46);
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_62, x_11, x_12, x_13, x_14, x_52);
x_19 = x_63;
goto block_26;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_dec(x_50);
x_65 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_49);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_49);
x_68 = l_Lean_Syntax_node1(x_49, x_67, x_66);
x_69 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_49);
x_70 = l_Lean_Syntax_node1(x_49, x_69, x_68);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_49);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_49);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_71);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_74 = l_Lean_Syntax_node3(x_49, x_73, x_70, x_72, x_46);
x_75 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_74, x_11, x_12, x_13, x_14, x_64);
x_19 = x_75;
goto block_26;
}
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_13, 5);
lean_inc(x_76);
x_77 = 0;
x_78 = l_Lean_SourceInfo_fromRef(x_76, x_77);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_14, x_45);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_82 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_78);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_82);
x_84 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
lean_inc(x_83);
x_85 = l_Lean_Syntax_node3(x_78, x_84, x_83, x_83, x_46);
x_86 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_85, x_11, x_12, x_13, x_14, x_80);
x_19 = x_86;
goto block_26;
}
}
}
block_271:
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_88);
x_89 = 0;
lean_inc(x_13);
x_90 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkSimpOnly___spec__1(x_30, x_89, x_11, x_12, x_13, x_14, x_15);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_get(x_14, x_92);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 1);
x_96 = lean_ctor_get(x_93, 0);
lean_dec(x_96);
x_97 = lean_mk_syntax_ident(x_91);
if (x_31 == 0)
{
if (x_32 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_free_object(x_93);
x_98 = lean_ctor_get(x_13, 5);
lean_inc(x_98);
x_99 = l_Lean_SourceInfo_fromRef(x_98, x_89);
lean_dec(x_98);
x_100 = lean_st_ref_get(x_14, x_95);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_100, 1);
x_103 = lean_ctor_get(x_100, 0);
lean_dec(x_103);
x_104 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_99);
lean_ctor_set_tag(x_100, 2);
lean_ctor_set(x_100, 1, x_104);
lean_ctor_set(x_100, 0, x_99);
x_105 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_99);
x_106 = l_Lean_Syntax_node1(x_99, x_105, x_100);
x_107 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_99);
x_108 = l_Lean_Syntax_node1(x_99, x_107, x_106);
x_109 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_99);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_107);
lean_ctor_set(x_110, 2, x_109);
x_111 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_112 = l_Lean_Syntax_node3(x_99, x_111, x_108, x_110, x_97);
x_113 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_112, x_11, x_12, x_13, x_14, x_102);
x_19 = x_113;
goto block_26;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_dec(x_100);
x_115 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_99);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_99);
x_118 = l_Lean_Syntax_node1(x_99, x_117, x_116);
x_119 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_99);
x_120 = l_Lean_Syntax_node1(x_99, x_119, x_118);
x_121 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_99);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_99);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_121);
x_123 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_124 = l_Lean_Syntax_node3(x_99, x_123, x_120, x_122, x_97);
x_125 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_124, x_11, x_12, x_13, x_14, x_114);
x_19 = x_125;
goto block_26;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_13, 5);
lean_inc(x_126);
x_127 = l_Lean_SourceInfo_fromRef(x_126, x_89);
lean_dec(x_126);
x_128 = lean_st_ref_get(x_14, x_95);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_130 = lean_ctor_get(x_128, 1);
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
x_132 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_127);
lean_ctor_set_tag(x_128, 2);
lean_ctor_set(x_128, 1, x_132);
lean_ctor_set(x_128, 0, x_127);
x_133 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_127);
x_134 = l_Lean_Syntax_node1(x_127, x_133, x_128);
x_135 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_127);
x_136 = l_Lean_Syntax_node1(x_127, x_135, x_134);
x_137 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_127);
lean_ctor_set_tag(x_93, 2);
lean_ctor_set(x_93, 1, x_137);
lean_ctor_set(x_93, 0, x_127);
x_138 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_127);
x_139 = l_Lean_Syntax_node1(x_127, x_138, x_93);
x_140 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_127);
x_141 = l_Lean_Syntax_node1(x_127, x_140, x_139);
lean_inc(x_127);
x_142 = l_Lean_Syntax_node1(x_127, x_135, x_141);
x_143 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_144 = l_Lean_Syntax_node3(x_127, x_143, x_136, x_142, x_97);
x_145 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_144, x_11, x_12, x_13, x_14, x_130);
x_19 = x_145;
goto block_26;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_146 = lean_ctor_get(x_128, 1);
lean_inc(x_146);
lean_dec(x_128);
x_147 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_127);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_127);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_127);
x_150 = l_Lean_Syntax_node1(x_127, x_149, x_148);
x_151 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_127);
x_152 = l_Lean_Syntax_node1(x_127, x_151, x_150);
x_153 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_127);
lean_ctor_set_tag(x_93, 2);
lean_ctor_set(x_93, 1, x_153);
lean_ctor_set(x_93, 0, x_127);
x_154 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_127);
x_155 = l_Lean_Syntax_node1(x_127, x_154, x_93);
x_156 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_127);
x_157 = l_Lean_Syntax_node1(x_127, x_156, x_155);
lean_inc(x_127);
x_158 = l_Lean_Syntax_node1(x_127, x_151, x_157);
x_159 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_160 = l_Lean_Syntax_node3(x_127, x_159, x_152, x_158, x_97);
x_161 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_160, x_11, x_12, x_13, x_14, x_146);
x_19 = x_161;
goto block_26;
}
}
}
else
{
lean_free_object(x_93);
if (x_32 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_162 = lean_ctor_get(x_13, 5);
lean_inc(x_162);
x_163 = l_Lean_SourceInfo_fromRef(x_162, x_89);
lean_dec(x_162);
x_164 = lean_st_ref_get(x_14, x_95);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_167 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_163);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_166);
lean_ctor_set(x_168, 2, x_167);
x_169 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
lean_inc(x_168);
x_170 = l_Lean_Syntax_node3(x_163, x_169, x_168, x_168, x_97);
x_171 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_170, x_11, x_12, x_13, x_14, x_165);
x_19 = x_171;
goto block_26;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_172 = lean_ctor_get(x_13, 5);
lean_inc(x_172);
x_173 = l_Lean_SourceInfo_fromRef(x_172, x_89);
lean_dec(x_172);
x_174 = lean_st_ref_get(x_14, x_95);
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_176 = lean_ctor_get(x_174, 1);
x_177 = lean_ctor_get(x_174, 0);
lean_dec(x_177);
x_178 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_179 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_173);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set(x_180, 2, x_179);
x_181 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_173);
lean_ctor_set_tag(x_174, 2);
lean_ctor_set(x_174, 1, x_181);
lean_ctor_set(x_174, 0, x_173);
x_182 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_173);
x_183 = l_Lean_Syntax_node1(x_173, x_182, x_174);
x_184 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_173);
x_185 = l_Lean_Syntax_node1(x_173, x_184, x_183);
lean_inc(x_173);
x_186 = l_Lean_Syntax_node1(x_173, x_178, x_185);
x_187 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_188 = l_Lean_Syntax_node3(x_173, x_187, x_180, x_186, x_97);
x_189 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_188, x_11, x_12, x_13, x_14, x_176);
x_19 = x_189;
goto block_26;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_190 = lean_ctor_get(x_174, 1);
lean_inc(x_190);
lean_dec(x_174);
x_191 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_192 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_173);
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_173);
lean_ctor_set(x_193, 1, x_191);
lean_ctor_set(x_193, 2, x_192);
x_194 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_173);
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_173);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_173);
x_197 = l_Lean_Syntax_node1(x_173, x_196, x_195);
x_198 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_173);
x_199 = l_Lean_Syntax_node1(x_173, x_198, x_197);
lean_inc(x_173);
x_200 = l_Lean_Syntax_node1(x_173, x_191, x_199);
x_201 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_202 = l_Lean_Syntax_node3(x_173, x_201, x_193, x_200, x_97);
x_203 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_202, x_11, x_12, x_13, x_14, x_190);
x_19 = x_203;
goto block_26;
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_93, 1);
lean_inc(x_204);
lean_dec(x_93);
x_205 = lean_mk_syntax_ident(x_91);
if (x_31 == 0)
{
if (x_32 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_206 = lean_ctor_get(x_13, 5);
lean_inc(x_206);
x_207 = l_Lean_SourceInfo_fromRef(x_206, x_89);
lean_dec(x_206);
x_208 = lean_st_ref_get(x_14, x_204);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_210 = x_208;
} else {
 lean_dec_ref(x_208);
 x_210 = lean_box(0);
}
x_211 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_207);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(2, 2, 0);
} else {
 x_212 = x_210;
 lean_ctor_set_tag(x_212, 2);
}
lean_ctor_set(x_212, 0, x_207);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_207);
x_214 = l_Lean_Syntax_node1(x_207, x_213, x_212);
x_215 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_207);
x_216 = l_Lean_Syntax_node1(x_207, x_215, x_214);
x_217 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_207);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_207);
lean_ctor_set(x_218, 1, x_215);
lean_ctor_set(x_218, 2, x_217);
x_219 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_220 = l_Lean_Syntax_node3(x_207, x_219, x_216, x_218, x_205);
x_221 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_220, x_11, x_12, x_13, x_14, x_209);
x_19 = x_221;
goto block_26;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_222 = lean_ctor_get(x_13, 5);
lean_inc(x_222);
x_223 = l_Lean_SourceInfo_fromRef(x_222, x_89);
lean_dec(x_222);
x_224 = lean_st_ref_get(x_14, x_204);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3;
lean_inc(x_223);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(2, 2, 0);
} else {
 x_228 = x_226;
 lean_ctor_set_tag(x_228, 2);
}
lean_ctor_set(x_228, 0, x_223);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2;
lean_inc(x_223);
x_230 = l_Lean_Syntax_node1(x_223, x_229, x_228);
x_231 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
lean_inc(x_223);
x_232 = l_Lean_Syntax_node1(x_223, x_231, x_230);
x_233 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_223);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_223);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_223);
x_236 = l_Lean_Syntax_node1(x_223, x_235, x_234);
x_237 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_223);
x_238 = l_Lean_Syntax_node1(x_223, x_237, x_236);
lean_inc(x_223);
x_239 = l_Lean_Syntax_node1(x_223, x_231, x_238);
x_240 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_241 = l_Lean_Syntax_node3(x_223, x_240, x_232, x_239, x_205);
x_242 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_241, x_11, x_12, x_13, x_14, x_225);
x_19 = x_242;
goto block_26;
}
}
else
{
if (x_32 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_243 = lean_ctor_get(x_13, 5);
lean_inc(x_243);
x_244 = l_Lean_SourceInfo_fromRef(x_243, x_89);
lean_dec(x_243);
x_245 = lean_st_ref_get(x_14, x_204);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_248 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_244);
x_249 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_249, 0, x_244);
lean_ctor_set(x_249, 1, x_247);
lean_ctor_set(x_249, 2, x_248);
x_250 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
lean_inc(x_249);
x_251 = l_Lean_Syntax_node3(x_244, x_250, x_249, x_249, x_205);
x_252 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_251, x_11, x_12, x_13, x_14, x_246);
x_19 = x_252;
goto block_26;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_253 = lean_ctor_get(x_13, 5);
lean_inc(x_253);
x_254 = l_Lean_SourceInfo_fromRef(x_253, x_89);
lean_dec(x_253);
x_255 = lean_st_ref_get(x_14, x_204);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = l_Lean_Elab_Tactic_tacticToDischarge___closed__11;
x_259 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_254);
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_254);
lean_ctor_set(x_260, 1, x_258);
lean_ctor_set(x_260, 2, x_259);
x_261 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10;
lean_inc(x_254);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(2, 2, 0);
} else {
 x_262 = x_257;
 lean_ctor_set_tag(x_262, 2);
}
lean_ctor_set(x_262, 0, x_254);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9;
lean_inc(x_254);
x_264 = l_Lean_Syntax_node1(x_254, x_263, x_262);
x_265 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6;
lean_inc(x_254);
x_266 = l_Lean_Syntax_node1(x_254, x_265, x_264);
lean_inc(x_254);
x_267 = l_Lean_Syntax_node1(x_254, x_258, x_266);
x_268 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
x_269 = l_Lean_Syntax_node3(x_254, x_268, x_260, x_267, x_205);
x_270 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_28, x_27, x_269, x_11, x_12, x_13, x_14, x_256);
x_19 = x_270;
goto block_26;
}
}
}
}
}
case 1:
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_10);
if (x_286 == 0)
{
uint8_t x_287; 
x_287 = !lean_is_exclusive(x_18);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_10, 0);
x_289 = lean_ctor_get(x_10, 1);
x_290 = lean_ctor_get(x_18, 0);
lean_inc(x_3);
x_291 = lean_local_ctx_find(x_3, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
lean_ctor_set(x_18, 0, x_10);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_18);
lean_ctor_set(x_292, 1, x_15);
x_19 = x_292;
goto block_26;
}
else
{
lean_free_object(x_18);
if (x_1 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_free_object(x_10);
x_293 = lean_ctor_get(x_291, 0);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_box(0);
x_295 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_288, x_293, x_3, x_289, x_294, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_293);
x_19 = x_295;
goto block_26;
}
else
{
uint8_t x_296; 
x_296 = !lean_is_exclusive(x_291);
if (x_296 == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_ctor_get(x_291, 0);
x_298 = l_Lean_LocalDecl_hasValue(x_297);
if (x_298 == 0)
{
lean_object* x_299; 
lean_dec(x_297);
lean_ctor_set(x_291, 0, x_10);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_291);
lean_ctor_set(x_299, 1, x_15);
x_19 = x_299;
goto block_26;
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_free_object(x_291);
lean_free_object(x_10);
x_300 = lean_box(0);
x_301 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_288, x_297, x_3, x_289, x_300, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_297);
x_19 = x_301;
goto block_26;
}
}
else
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_291, 0);
lean_inc(x_302);
lean_dec(x_291);
x_303 = l_Lean_LocalDecl_hasValue(x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_302);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_10);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_15);
x_19 = x_305;
goto block_26;
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_free_object(x_10);
x_306 = lean_box(0);
x_307 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_288, x_302, x_3, x_289, x_306, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_302);
x_19 = x_307;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_10, 0);
x_309 = lean_ctor_get(x_10, 1);
x_310 = lean_ctor_get(x_18, 0);
lean_inc(x_310);
lean_dec(x_18);
lean_inc(x_3);
x_311 = lean_local_ctx_find(x_3, x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_10);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_15);
x_19 = x_313;
goto block_26;
}
else
{
if (x_1 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_free_object(x_10);
x_314 = lean_ctor_get(x_311, 0);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_box(0);
x_316 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_308, x_314, x_3, x_309, x_315, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_314);
x_19 = x_316;
goto block_26;
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_317 = lean_ctor_get(x_311, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 x_318 = x_311;
} else {
 lean_dec_ref(x_311);
 x_318 = lean_box(0);
}
x_319 = l_Lean_LocalDecl_hasValue(x_317);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_317);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_10);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_15);
x_19 = x_321;
goto block_26;
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_318);
lean_free_object(x_10);
x_322 = lean_box(0);
x_323 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_308, x_317, x_3, x_309, x_322, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_317);
x_19 = x_323;
goto block_26;
}
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_324 = lean_ctor_get(x_10, 0);
x_325 = lean_ctor_get(x_10, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_10);
x_326 = lean_ctor_get(x_18, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_327 = x_18;
} else {
 lean_dec_ref(x_18);
 x_327 = lean_box(0);
}
lean_inc(x_3);
x_328 = lean_local_ctx_find(x_3, x_326);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_324);
lean_ctor_set(x_329, 1, x_325);
if (lean_is_scalar(x_327)) {
 x_330 = lean_alloc_ctor(1, 1, 0);
} else {
 x_330 = x_327;
}
lean_ctor_set(x_330, 0, x_329);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_15);
x_19 = x_331;
goto block_26;
}
else
{
lean_dec(x_327);
if (x_1 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_328, 0);
lean_inc(x_332);
lean_dec(x_328);
x_333 = lean_box(0);
x_334 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_324, x_332, x_3, x_325, x_333, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_332);
x_19 = x_334;
goto block_26;
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_335 = lean_ctor_get(x_328, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_336 = x_328;
} else {
 lean_dec_ref(x_328);
 x_336 = lean_box(0);
}
x_337 = l_Lean_LocalDecl_hasValue(x_335);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_335);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_324);
lean_ctor_set(x_338, 1, x_325);
if (lean_is_scalar(x_336)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_336;
}
lean_ctor_set(x_339, 0, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_15);
x_19 = x_340;
goto block_26;
}
else
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_336);
x_341 = lean_box(0);
x_342 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_324, x_335, x_3, x_325, x_341, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_335);
x_19 = x_342;
goto block_26;
}
}
}
}
}
case 2:
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_10);
if (x_343 == 0)
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_18);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_345 = lean_ctor_get(x_10, 0);
x_346 = lean_ctor_get(x_18, 1);
x_347 = lean_ctor_get(x_18, 0);
lean_dec(x_347);
x_348 = lean_array_push(x_345, x_346);
lean_ctor_set(x_10, 0, x_348);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_10);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 0, x_349);
x_19 = x_18;
goto block_26;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_350 = lean_ctor_get(x_10, 0);
x_351 = lean_ctor_get(x_18, 1);
lean_inc(x_351);
lean_dec(x_18);
x_352 = lean_array_push(x_350, x_351);
lean_ctor_set(x_10, 0, x_352);
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_10);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_15);
x_19 = x_354;
goto block_26;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_355 = lean_ctor_get(x_10, 0);
x_356 = lean_ctor_get(x_10, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_10);
x_357 = lean_ctor_get(x_18, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_358 = x_18;
} else {
 lean_dec_ref(x_18);
 x_358 = lean_box(0);
}
x_359 = lean_array_push(x_355, x_357);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_356);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
if (lean_is_scalar(x_358)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_358;
 lean_ctor_set_tag(x_362, 0);
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_15);
x_19 = x_362;
goto block_26;
}
}
default: 
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_18);
if (x_363 == 0)
{
lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_18, 0);
lean_dec(x_364);
x_365 = !lean_is_exclusive(x_10);
if (x_365 == 0)
{
lean_object* x_366; 
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_10);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_18);
lean_ctor_set(x_366, 1, x_15);
x_19 = x_366;
goto block_26;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_10, 0);
x_368 = lean_ctor_get(x_10, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_10);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_369);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_18);
lean_ctor_set(x_370, 1, x_15);
x_19 = x_370;
goto block_26;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_18);
x_371 = lean_ctor_get(x_10, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_10, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_373 = x_10;
} else {
 lean_dec_ref(x_10);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_15);
x_19 = x_376;
goto block_26;
}
}
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_9, x_23);
x_9 = x_24;
x_10 = x_22;
x_15 = x_21;
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
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4;
lean_inc(x_16);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_syntax_ident(x_11);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_17 = lean_box(0);
x_18 = lean_array_size(x_16);
x_19 = 0;
x_20 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__2;
lean_inc(x_7);
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(x_2, x_10, x_11, x_15, x_16, x_17, x_16, x_18, x_19, x_20, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_7, 5);
lean_inc(x_26);
x_27 = 0;
x_28 = l_Lean_SourceInfo_fromRef(x_26, x_27);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_8, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3;
lean_inc(x_28);
lean_ctor_set_tag(x_29, 2);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_28);
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
x_35 = l_Lean_Syntax_node1(x_28, x_34, x_29);
x_36 = lean_array_push(x_25, x_35);
x_37 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(x_10, x_3, x_37, x_36, x_38, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__2___closed__3;
lean_inc(x_28);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6;
x_44 = l_Lean_Syntax_node1(x_28, x_43, x_42);
x_45 = lean_array_push(x_25, x_44);
x_46 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_47 = lean_box(0);
x_48 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(x_10, x_3, x_46, x_45, x_47, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_dec(x_21);
x_50 = lean_ctor_get(x_22, 0);
lean_inc(x_50);
lean_dec(x_22);
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_array_size(x_51);
x_53 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_mkSimpOnly___spec__8(x_52, x_19, x_51, x_5, x_6, x_7, x_8, x_49);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Array_append___rarg(x_50, x_54);
lean_dec(x_54);
x_57 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_addDeclToUnfoldOrTheorem___closed__1;
x_58 = lean_box(0);
x_59 = l_Lean_Elab_Tactic_mkSimpOnly___lambda__1(x_10, x_3, x_57, x_56, x_58, x_5, x_6, x_7, x_8, x_55);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_56);
return x_59;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__6(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
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
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6;
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
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6;
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
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6;
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
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabSimpArgs___spec__6___closed__8);
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
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__1 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__1);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__2 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__2);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__3 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__3);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__4 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__4);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__5 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__5);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__6);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__7 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261____closed__7);
if (builtin) {res = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Simp___hyg_6261_(lean_io_mk_world());
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
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___lambda__2___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__9);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkSimpOnly___spec__7___closed__10);
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
